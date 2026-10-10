import OAI.Geometry.SurfaceImmersion.Primitive.JetVelocityCoordinates
import OAI.Geometry.SurfaceImmersion.Primitive.VelocityCoordinateData
import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicExpansionInit

namespace OAI

/-! Convert a geometric second-jet velocity loop into the exact family of
Euclidean data used by the supported finite periodic recursion. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates CovarianceCorrector
open LocalPeriodicExpansion LocalPeriodicCalculus
local notation "ι" => JetVelocityCoordinates.toEuclidean

def normal (J : LowJet) : RVec 4 := realNormalPart (slot 2 J) (slot 6 J) (slot 1 J)
def tangent (J : LowJet) : RVec 4 := slot 1 J - normal J

/-- The actual geometric hypotheses on the second-jet neighborhood. The
first and second derivatives are fixed coordinate projections of that jet. -/
structure Loop (O : TopologicalSpace.Opens LowJet) where
  amplitude : LowJet → ℝ
  smoothAmplitude : ContDiffOn ℝ ∞ amplitude O
  velocity : LowJet × ℝ → RVec 4
  smoothVelocity : ContDiffOn ℝ ∞ velocity (O ×ˢ univ)
  periodic : ∀ J ∈ O, Function.Periodic (fun t => velocity (J, t)) 1
  gram_ne : ∀ J ∈ O, NormalFrame.gramDet (slot 2 J) (slot 6 J) ≠ 0
  nonzero : ∀ J ∈ O, normal J ≠ 0 ∨ amplitude J ≠ 0
  perpY : ∀ J ∈ O, ∀ t, slot 2 J ⬝ᵥ velocity (J, t) = 0
  perpC : ∀ J ∈ O, ∀ t, slot 6 J ⬝ᵥ velocity (J, t) = 0
  length : ∀ J ∈ O, ∀ t, velocity (J, t) ⬝ᵥ velocity (J, t) =
    normal J ⬝ᵥ normal J + amplitude J ^ 2
  mean : ∀ J ∈ O, (∫ t in 0..1, velocity (J, t)) = normal J

namespace Loop
variable {O : TopologicalSpace.Opens LowJet} (l : Loop O)

include l in
lemma smoothNormal : ContDiffOn ℝ ∞ normal O := by
  intro J hJ
  exact (contDiffAt_realNormalPart (slot_smooth 2).contDiffAt
    (slot_smooth 6).contDiffAt (slot_smooth 1).contDiffAt (l.gram_ne J hJ)).contDiffWithinAt

include l in
lemma smoothTangent : ContDiffOn ℝ ∞ tangent O := (slot_smooth 1).contDiffOn.sub l.smoothNormal

def q (J : LowJet) : ℝ := normal J ⬝ᵥ normal J + l.amplitude J ^ 2

lemma smoothQ : ContDiffOn ℝ ∞ l.q O :=
  (VelocityFrame.dot_smoothOn l.smoothNormal l.smoothNormal).add (l.smoothAmplitude.pow 2)

lemma q_pos {J : LowJet} (hJ : J ∈ O) : 0 < l.q J := by
  exact Real.sqrt_pos.mp (VelocityFrame.velocityRadius_pos (l.nonzero J hJ))

def euclideanVelocity : LowJet → C(Period, Euclidean) :=
  bundleOn (fun z => ι (l.velocity z)) O O.isOpen
    (JetVelocityCoordinates.toEuclidean.contDiff.comp_contDiffOn l.smoothVelocity)
    (fun J hJ t => congrArg ι (l.periodic J hJ t))

lemma euclideanVelocity_apply {J : LowJet} (hJ : J ∈ O) (t : ℝ) :
    l.euclideanVelocity J (t : Period) = ι (l.velocity (J, t)) :=
  bundleOn_apply _ _ _ _ _ hJ t

lemma euclideanVelocity_smooth :
    ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => l.euclideanVelocity z.1 (z.2 : Period))
      (O ×ˢ univ) := bundleOn_smooth _ _ _ _ _

lemma euclideanVelocity_mean {J : LowJet} (hJ : J ∈ O) :
    average (l.euclideanVelocity J) = ι (normal J) := by
  rw [average, ← PeriodicPrimitive.integral_lift_eq_haar]
  simp only [l.euclideanVelocity_apply hJ]
  have hi : IntervalIntegrable (fun t => l.velocity (J, t)) MeasureTheory.volume 0 1 :=
    (smooth_slice O.isOpen l.smoothVelocity hJ).continuous.intervalIntegrable 0 1
  exact (JetVelocityCoordinates.toEuclidean.toContinuousLinearMap.intervalIntegral_comp_comm hi).trans
    (congrArg ι (l.mean J hJ))

lemma euclideanVelocity_length {J : LowJet} (hJ : J ∈ O) (t : Period) :
    inner ℝ (l.euclideanVelocity J t) (l.euclideanVelocity J t) = l.q J := by
  refine Quotient.inductionOn' t ?_
  intro t
  rw [l.euclideanVelocity_apply hJ, inner_toEuclidean]
  exact l.length J hJ t

def plane (J : LowJet) : Submodule ℝ Euclidean :=
  LinearMap.ker (innerSL ℝ (ι (slot 2 J))).toLinearMap ⊓
    LinearMap.ker (innerSL ℝ (ι (slot 6 J))).toLinearMap

lemma mem_plane {J : LowJet} {w : Euclidean} :
    w ∈ plane J ↔ inner ℝ (ι (slot 2 J)) w = 0 ∧
      inner ℝ (ι (slot 6 J)) w = 0 := Iff.rfl

lemma tangent_perp {J : LowJet} {w : Euclidean} (hw : w ∈ plane J) :
    inner ℝ (ι (tangent J)) w = 0 := by
  obtain ⟨hy, hc⟩ := mem_plane.mp hw
  have hw' : ι (JetVelocityCoordinates.toEuclidean.symm w) = w := JetVelocityCoordinates.toEuclidean.apply_symm_apply w
  rw [← hw', inner_toEuclidean] at hy hc ⊢
  exact tangential_part_perp _ _ _ _ hy hc

/-- Pulling back through the actual second jet supplies the differentiated
constraint `Y_y=C`, rather than adding that constraint as a new input. -/
def geometry {S : TopologicalSpace.Opens JetPolynomial.Base}
    (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O) : Geometry (E := Euclidean) S (coordinateVector 1) where
  plane p := plane (lowJet G p)
  Y p := ι (slot 2 (lowJet G p))
  C p := ι (slot 6 (lowJet G p))
  X₀ p := ι (tangent (lowJet G p))
  smoothY := (JetVelocityCoordinates.toEuclidean.contDiff.comp ((slot_smooth 2).comp (lowJet_smooth hG))).contDiffOn
  smoothC := (JetVelocityCoordinates.toEuclidean.contDiff.comp ((slot_smooth 6).comp (lowJet_smooth hG))).contDiffOn
  smoothX₀ := JetVelocityCoordinates.toEuclidean.contDiff.comp_contDiffOn
    (l.smoothTangent.comp (lowJet_smooth hG).contDiffOn hGO)
  derivativeY p _ := euclidean_y_derivative hG p
  gram_ne p hp := by rw [gram_toEuclidean]; exact l.gram_ne _ (hGO hp)
  perpY _ _ _ hw := (mem_plane.mp hw).1
  perpC _ _ _ hw := (mem_plane.mp hw).2
  perpX₀ _ _ _ hw := tangent_perp hw
  V := Family.ofLocal (fun p => l.euclideanVelocity (lowJet G p))
    (l.euclideanVelocity_smooth.comp
      ((lowJet_smooth hG).contDiffOn.comp contDiffOn_fst (fun z _ => mem_univ z.1)
        |>.prodMk contDiffOn_snd) (fun z hz => ⟨hGO hz.1, mem_univ z.2⟩))
  V_mem p hp t := by
    rw [Family.ofLocal_apply _ _ hp]
    refine Quotient.inductionOn' t ?_
    intro t
    rw [l.euclideanVelocity_apply (hGO hp)]
    apply mem_plane.mpr
    constructor
    · rw [inner_toEuclidean]; exact l.perpY _ (hGO hp) t
    · rw [inner_toEuclidean]; exact l.perpC _ (hGO hp) t
  q p := l.q (lowJet G p)
  smoothq := l.smoothQ.comp (lowJet_smooth hG).contDiffOn hGO
  q_pos _ hp := l.q_pos (hGO hp)
  circle p hp t := by
    rw [Family.ofLocal_apply _ _ hp]
    exact l.euclideanVelocity_length (hGO hp) t

end Loop
end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
