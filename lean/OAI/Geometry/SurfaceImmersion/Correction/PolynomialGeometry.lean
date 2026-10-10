import OAI.Geometry.SurfaceImmersion.Correction.PolynomialJetSmoothness
import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicExpansionInit

namespace OAI

/-! Low-jet geometry and the initial primitive in the actual periodic family
are represented by the corresponding coordinate polynomial expressions. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open LocalPeriodicExpansion CovarianceCorrector

namespace VectorExpression

def sub (R T : VectorExpression) : VectorExpression := fun i => (R i).sub (T i)

lemma represents_sub {S : TopologicalSpace.Opens Base} {G : Base → Space}
    {R T : VectorExpression} {U W : Family S R4} (hR : Represents G R U)
    (hT : Represents G T W) : Represents G (R.sub T) (U - W) := by
  intro i p hp t
  simp only [sub, Expression.eval_sub, hR i p hp t, hT i p hp t, Family.sub_apply]
  rfl

end VectorExpression

namespace MetricPolynomial

def velocity (V : LowJet → C(Period, R4)) : VectorExpression :=
  fun a => .coeff (fun z => V z.1 (z.2 : Period) a)

lemma represents_longitudinal {S : TopologicalSpace.Opens Base} {G : Base → Space}
    {v : Base} (g : Geometry (E := R4) S v) (X₀ : LowJet → R4) (V : LowJet → C(Period, R4))
    (hX : ∀ p ∈ S, g.X₀ p = X₀ (lowJet G p)) (hV : ∀ p ∈ S, g.V.val p = V (lowJet G p)) :
    VectorExpression.Represents G (longitudinal X₀ V) g.longitudinal := by
  intro i p hp t
  change (X₀ (lowJet G p) + V (lowJet G p) (t : Period)) i = _
  rw [Geometry.longitudinal, Family.add_apply, Family.constant_apply _ _ hp,
    hX p hp, hV p hp]

lemma represents_transverse {S : TopologicalSpace.Opens Base} {G : Base → Space}
    {v : Base} (g : Geometry (E := R4) S v) (Y : LowJet → R4)
    (hY : ∀ p ∈ S, g.Y p = Y (lowJet G p)) :
    VectorExpression.Represents G (transverse Y) g.transverse := by
  intro i p hp t
  change Y (lowJet G p) i = _
  rw [Geometry.transverse, Family.constant_apply _ _ hp, hY p hp]

lemma represents_velocity {S : TopologicalSpace.Opens Base} {G : Base → Space}
    {v : Base} (g : Geometry (E := R4) S v) (V : LowJet → C(Period, R4))
    (hV : ∀ p ∈ S, g.V.val p = V (lowJet G p)) :
    VectorExpression.Represents G (velocity V) g.V := by
  intro i p hp t
  change V (lowJet G p) (t : Period) i = _
  rw [hV p hp]

lemma smooth_velocity {O : Set LowJet} {V : LowJet → C(Period, R4)}
    (hV : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ)) :
    (velocity V).SmoothCoeffs O := by
  intro a
  let L : R4 →L[ℝ] ℝ := EuclideanSpace.proj a
  exact L.contDiff.comp_contDiffOn hV

lemma represents_initial {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hQ : Set.MapsTo (lowJet G) S O) {v : Base}
    (g : Geometry (E := R4) S v) {V : LowJet → C(Period, R4)}
    (hVs : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hV : ∀ p ∈ S, g.V.val p = V (lowJet G p)) :
    VectorExpression.Represents G (initial V) g.initial := by
  have hs := smooth_velocity hVs
  have hv := represents_velocity g V hV
  have hm := VectorExpression.represents_mean hO hQ hs hv
  have hc := VectorExpression.represents_sub hv hm
  have hcs : ((velocity V).sub (velocity V).mean).SmoothCoeffs O := by
    intro a
    exact Expression.smoothCoeffs_fluct hO (hs a)
  exact VectorExpression.represents_primitive hO hQ hcs hc (fun p _ => g.V.centered_mean_zero p)

end MetricPolynomial
end ClosedSurfaceR4.JetPolynomial

end

end OAI
