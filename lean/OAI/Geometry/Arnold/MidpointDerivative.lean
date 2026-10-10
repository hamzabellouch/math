import OAI.Geometry.Arnold.FixedCount

namespace OAI

universe uE

noncomputable section
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter

namespace ArnoldCounterexample.Midpoint
open scoped ContDiff Topology NNReal
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma resolvent_equilibrium (X : E → E) {C : ℝ≥0} (hX : LipschitzWith C X)
    (τ : ℝ → ℝ) (hτ : ∀ t, ‖τ t‖*C < 1) (t : ℝ) (z : E) (hz : X z = 0) :
    resolvent X hX τ hτ (t,z) = z := by
  symm
  apply resolvent_unique
  simp [hz]

lemma step_equilibrium (X : E → E) {C : ℝ≥0} (hX : LipschitzWith C X)
    (τ : ℝ → ℝ) (hτ : ∀ t, ‖τ t‖*C < 1) (t : ℝ) (z : E) (hz : X z = 0) :
    step X hX τ hτ (t,z) = z := by
  rw [step_center, resolvent_equilibrium _ hX τ hτ t z hz, hz, smul_zero, add_zero]

lemma resolvent_right_inverse (X : E → E) {C : ℝ≥0} (hX : LipschitzWith C X)
    (τ : ℝ → ℝ) (hτ : ∀ t, ‖τ t‖*C < 1) (t : ℝ) (z : E) :
    resolvent X hX τ hτ (t, z - τ t • X z) = z := by
  symm
  apply resolvent_unique
  simp

lemma resolvent_kernel (X : E → E) {C : ℝ≥0} (hX : LipschitzWith C X)
    (hXs : ContDiff ℝ ∞ X) (τ : ℝ → ℝ) (hτ : ∀ t, ‖τ t‖*C < 1)
    (hτs : ContDiff ℝ ∞ τ) (t : ℝ) (z v : E) (hz : X z = 0)
    (hv : fderiv ℝ X z v = 0) :
    fderiv ℝ (fun w ↦ resolvent X hX τ hτ (t,w)) z v = v := by
  let R : E → E := fun w ↦ resolvent X hX τ hτ (t,w)
  have hR : ContDiff ℝ ∞ R := (resolvent_smooth _ hX hXs _ hτ hτs).comp (contDiff_const.prodMk contDiff_id)
  have hU := (hasFDerivAt_id (𝕜 := ℝ) z).sub ((hXs.differentiable (by simp) z).hasFDerivAt.const_smul (τ t))
  have he : (fun w ↦ R (w - τ t • X w)) = id := funext (resolvent_right_inverse _ hX τ hτ t)
  have hUZ : z - τ t • X z = z := by simp [hz]
  have hd := (hR.differentiable (by simp) (z - τ t • X z)).hasFDerivAt.comp z hU
  change HasFDerivAt (fun w ↦ R (w - τ t • X w)) _ z at hd
  rw [he,hUZ] at hd
  have h := congrArg (fun L : E →L[ℝ] E ↦ L v) (hd.unique (hasFDerivAt_id z))
  simpa only [ContinuousLinearMap.comp_apply, sub_apply,
    ContinuousLinearMap.id_apply, smul_apply, hv, smul_zero, sub_zero] using h

lemma step_kernel (X : E → E) {C : ℝ≥0} (hX : LipschitzWith C X)
    (hXs : ContDiff ℝ ∞ X) (τ : ℝ → ℝ) (hτ : ∀ t, ‖τ t‖*C < 1)
    (hτs : ContDiff ℝ ∞ τ) (t : ℝ) (z v : E) (hz : X z = 0)
    (hv : fderiv ℝ X z v = 0) :
    fderiv ℝ (fun w ↦ step X hX τ hτ (t,w)) z v = v := by
  have hR : ContDiff ℝ ∞ (fun w ↦ resolvent X hX τ hτ (t,w)) :=
    (resolvent_smooth _ hX hXs _ hτ hτs).comp (contDiff_const.prodMk contDiff_id)
  have hd := ((hR.differentiable (by simp) z).hasFDerivAt.const_smul (2:ℝ)).sub (hasFDerivAt_id z)
  change HasFDerivAt (fun w ↦ step X hX τ hτ (t,w)) _ z at hd
  rw [hd.fderiv]
  change (2:ℝ) • fderiv ℝ (fun w ↦ resolvent X hX τ hτ (t,w)) z v - v = v
  rw [resolvent_kernel _ hX hXs τ hτ hτs t z v hz hv]
  module

end ArnoldCounterexample.Midpoint

end

end OAI
