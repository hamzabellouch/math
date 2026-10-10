import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.BoxCoding
import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.FieldBounds
import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.CompactFamilies

namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def ForwardEq (v w : Field F) : Prop := ∀ t, 0 ≤ t → v t = w t

lemma ForwardEq.mixedD {v w : Field F} (h : ForwardEq v w) (a : MultiIndex) :
    ForwardEq (BalancedTransport.mixedD a v) (BalancedTransport.mixedD a w) := by
  induction a with
  | nil => exact h
  | cons i a ha =>
    intro t ht
    funext x
    cases i with
    | none =>
      change derivWithin (fun s => BalancedTransport.mixedD a v s x) (Ici 0) t =
        derivWithin (fun s => BalancedTransport.mixedD a w s x) (Ici 0) t
      exact derivWithin_congr (s := Ici (0 : ℝ))
        (fun s hs => congrFun (ha s hs) x) (congrFun (ha t ht) x)
    | some i =>
      change fderiv ℝ (BalancedTransport.mixedD a v t) x _ = fderiv ℝ (BalancedTransport.mixedD a w t) x _
      rw [ha t ht]

lemma ForwardEq.smooth {v w : Field F} (h : ForwardEq v w) (hv : Smooth v) : Smooth w := by
  apply hv.congr
  intro z hz
  exact congrFun (h z.1 hz.1).symm z.2

lemma JointSmooth.smooth {v : Field F} (hv : JointSmooth v) : Smooth v := hv.contDiffOn

lemma ForwardEq.boundedMixed {v w : Field F} (h : ForwardEq v w)
    (hv : BoundedMixed v) : BoundedMixed w := by
  intro a
  obtain ⟨C, hC, hbound⟩ := hv a
  refine ⟨C, hC, fun t ht x => ?_⟩
  rw [← (h.mixedD a) t ht]
  exact hbound t ht x

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
lemma ForwardEq.repeatsAfter {v w : Field F} (h : ForwardEq v w)
    (hp : RepeatsAfter 1 v) : RepeatsAfter 1 w := by
  intro t ht
  rw [← h t (by linarith), ← h (t+1) (by linarith)]
  exact hp t ht

lemma JointSmooth.laplacian {v : Velocity} (hv : JointSmooth v) :
    JointSmooth (BalancedTransport.laplacian v) := JointSmooth.sum (fun i => (hv.spaceD i).spaceD i)

lemma JointSmooth.convection {v : Velocity} (hv : JointSmooth v) :
    JointSmooth (BalancedTransport.convection v) := by
  apply JointSmooth.sum
  intro i
  exact (contDiff_pi.mp hv i).smul (hv.spaceD i)

def fullInertial (v : Velocity) : Velocity := fun t x => BalancedTransport.Geometry.fullTimeD v t x + BalancedTransport.convection v t x

lemma JointSmooth.fullInertial {v : Velocity} (hv : JointSmooth v) :
    JointSmooth (fullInertial v) := hv.fullTimeD.add hv.convection

lemma JointSmooth.viscousCoefficient {v : Velocity} (hv : JointSmooth v) :
    JointSmooth (viscousCoefficient v) := hv.laplacian.neg

lemma fullInertial_forwardEq {v : Velocity} (hv : JointSmooth v) :
    ForwardEq (fullInertial v) (inertialCoefficient v) := by
  intro t ht
  funext x
  change BalancedTransport.Geometry.fullTimeD v t x + BalancedTransport.convection v t x = timeD v t x + BalancedTransport.convection v t x
  rw [show BalancedTransport.Geometry.fullTimeD v t x = timeD v t x from fullMixedD_eq_mixedD hv [none] t ht x]

lemma SpatiallySupported.laplacian {K : Set Space} {v : Velocity}
    (h : SpatiallySupported K v) (hK : IsClosed K) : SpatiallySupported K (BalancedTransport.laplacian v) := by
  intro t x hx
  exact Finset.sum_eq_zero (fun i _ => ((h.spaceD hK i).spaceD hK i) t x hx)

lemma SpatiallySupported.convection {K : Set Space} {v : Velocity}
    (h : SpatiallySupported K v) : SpatiallySupported K (BalancedTransport.convection v) := by
  intro t x hx
  change ∑ i, (v t x i) • BalancedTransport.spaceD i v t x = 0
  simp [h t x hx]

lemma SpatiallySupported.fullInertial {K : Set Space} {v : Velocity}
    (h : SpatiallySupported K v) : SpatiallySupported K (fullInertial v) := by
  intro t x hx
  change BalancedTransport.Geometry.fullTimeD v t x + BalancedTransport.convection v t x = 0
  rw [h.fullTimeD t x hx, h.convection t x hx, add_zero]

lemma SpatiallySupported.viscousCoefficient {K : Set Space} {v : Velocity}
    (h : SpatiallySupported K v) (hK : IsClosed K) :
    SpatiallySupported K (viscousCoefficient v) := by
  intro t x hx
  change -BalancedTransport.laplacian v t x = 0
  rw [h.laplacian hK t x hx, neg_zero]

lemma RepeatsAfter.laplacian {T : ℝ} {v : Velocity} (h : RepeatsAfter T v) :
    RepeatsAfter T (BalancedTransport.laplacian v) := by
  intro t ht
  funext x
  change (∑ i, BalancedTransport.spaceD i (BalancedTransport.spaceD i v) (t + 1) x) = ∑ i, BalancedTransport.spaceD i (BalancedTransport.spaceD i v) t x
  apply Finset.sum_congr rfl
  intro i _
  exact congrFun (((h.spaceD i).spaceD i) t ht) x

lemma RepeatsAfter.convection {T : ℝ} {v : Velocity} (h : RepeatsAfter T v) :
    RepeatsAfter T (BalancedTransport.convection v) := by
  intro t ht
  funext x
  change (∑ i, v (t + 1) x i • BalancedTransport.spaceD i v (t + 1) x) = ∑ i, v t x i • BalancedTransport.spaceD i v t x
  simp only [h t ht, (h.spaceD _) t ht]

lemma RepeatsAfter.fullInertial {T : ℝ} {v : Velocity} (h : RepeatsAfter T v)
    (hv : JointSmooth v) : RepeatsAfter T (fullInertial v) := by
  intro t ht
  funext x
  change BalancedTransport.Geometry.fullTimeD v (t+1) x + BalancedTransport.convection v (t+1) x = BalancedTransport.Geometry.fullTimeD v t x + BalancedTransport.convection v t x
  rw [h.fullTimeD hv t ht, h.convection t ht]

lemma RepeatsAfter.viscousCoefficient {T : ℝ} {v : Velocity} (h : RepeatsAfter T v) :
    RepeatsAfter T (viscousCoefficient v) := by
  intro t ht
  funext x
  change -BalancedTransport.laplacian v (t+1) x = -BalancedTransport.laplacian v t x
  rw [h.laplacian t ht]

theorem prescribed_residual_regularity {K : Set Space} (hK : IsCompact K) {U : Velocity}
    (hU : JointSmooth U) (hs : SpatiallySupported K U) (hp : RepeatsAfter 1 U)
    (hzero : ∀ x, U 0 x = 0) (hdiv : ∀ t, 0 ≤ t → ∀ x, div U t x = 0) :
    Smooth (inertialCoefficient U) ∧ Smooth (viscousCoefficient U) ∧
    CommonCompactSupport U (inertialCoefficient U) (viscousCoefficient U) ∧
    BoundedMixed U ∧ BoundedMixed (inertialCoefficient U) ∧ BoundedMixed (viscousCoefficient U) ∧
    PeriodicAfterOne U ∧
    ∀ ν : ℝ, let f := affineForce (inertialCoefficient U) (viscousCoefficient U) ν
      ZeroDataSolution ν f U (fun _ _ => 0) ∧
      Smooth f ∧ BoundedMixed f ∧ PeriodicAfterOne f := by
  have hf₀ := hU.fullInertial
  have hf₁ := hU.viscousCoefficient
  have he := fullInertial_forwardEq hU
  have hs₀ := hs.fullInertial
  have hs₁ := hs.viscousCoefficient hK.isClosed
  have hp₀ := hp.fullInertial hU
  have hp₁ := hp.viscousCoefficient
  refine ⟨he.smooth hf₀.smooth, hf₁.smooth, ⟨K, hK, ?_⟩,
    boundedMixed_of_compact_repeating hK hU hs hp,
    he.boundedMixed (boundedMixed_of_compact_repeating hK hf₀ hs₀ hp₀),
    boundedMixed_of_compact_repeating hK hf₁ hs₁ hp₁, ?_, ?_⟩
  · intro t ht x hx
    exact ⟨hs t x hx, (congrFun (he t ht) x).symm.trans (hs₀ t x hx), hs₁ t x hx⟩
  · intro t ht x
    exact congrFun (hp t ht) x
  · intro ν
    dsimp only
    let g : Velocity := fun t x => fullInertial U t x + ν • viscousCoefficient U t x
    have hg : JointSmooth g := hf₀.add (ContDiff.smul (f := fun _ : ℝ × Space => ν) contDiff_const hf₁)
    have hgs : SpatiallySupported K g := by
      intro t x hx
      dsimp [g]
      rw [hs₀ t x hx, hs₁ t x hx, smul_zero, add_zero]
    have hgp : RepeatsAfter 1 g := by
      intro t ht
      ext x i
      dsimp [g]
      rw [hp₀ t ht, hp₁ t ht]
    have hge : ForwardEq g (affineForce (inertialCoefficient U) (viscousCoefficient U) ν) := by
      intro t ht
      ext x i
      dsimp [g, affineForce]
      rw [he t ht]
    refine ⟨residual_zero_pressure_solution ν U hU.smooth hzero hdiv,
      hge.smooth hg.smooth,
      hge.boundedMixed (boundedMixed_of_compact_repeating hK hg hgs hgp), ?_⟩
    intro t ht x
    exact congrFun (hge.repeatsAfter hgp t ht) x

end BalancedTransport.Geometry
end

end OAI
