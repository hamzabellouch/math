import OAI.Geometry.SurfaceImmersion.Geometry.RegularZeroStability

namespace OAI

/-! Small scalar-weighted translations preserve compact regular zero sets. -/
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
local instance translationScalarNormed : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance translationScalarSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance translationTargetNormed : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance translationTargetSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance

theorem compact_translation_stability {f : E → F} {χ : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hχ : ContDiff ℝ ∞ χ)
    {K : Set E} (hK : IsCompact K)
    (hreg : ∀ x ∈ K, f x = 0 → Function.Surjective (fderiv ℝ f x)) :
    ∃ δ > 0, ∀ a : F, ‖a‖ < δ → ∀ x ∈ K, f x+χ x • a = 0 →
      Function.Surjective (fderiv ℝ (fun y => f y+χ y • a) x) := by
  obtain ⟨ε,hε,hεreg⟩ := compact_regular_zero_stability hf hK hreg
  obtain ⟨M₀,hM₀⟩ := hK.exists_bound_of_continuousOn hχ.continuous.continuousOn
  obtain ⟨M₁,hM₁⟩ := hK.exists_bound_of_continuousOn (hχ.continuous_fderiv (by simp)).continuousOn
  let B := max M₀ (max M₁ 0)+1
  have hB : 0 < B := by dsimp [B]; have := le_max_right M₀ (max M₁ 0); have := le_max_right M₁ 0; linarith
  refine ⟨ε/B,div_pos hε hB,?_⟩
  intro a ha
  have hab : B*‖a‖ < ε := by
    simpa only [mul_comm] using (lt_div_iff₀ hB).mp ha
  apply hεreg (fun y => f y+χ y • a)
  · intro x hx
    rw [add_sub_cancel_left,norm_smul]
    have hχB : ‖χ x‖ ≤ B := (hM₀ x hx).trans (by dsimp [B]; linarith [le_max_left M₀ (max M₁ 0)])
    exact (mul_le_mul_of_nonneg_right hχB (norm_nonneg a)).trans_lt hab
  · intro x hx
    have hd := ((hf.differentiable (by simp) x).hasFDerivAt.add
      ((hχ.differentiable (by simp) x).hasFDerivAt.smul_const a)).fderiv
    change ‖fderiv ℝ (f + fun y => χ y • a) x-fderiv ℝ f x‖ < ε
    rw [hd,add_sub_cancel_left,ContinuousLinearMap.norm_smulRight_apply]
    have hχB : ‖fderiv ℝ χ x‖ ≤ B := (hM₁ x hx).trans (by
      dsimp [B]; linarith [le_max_right M₀ (max M₁ 0),le_max_left M₁ 0])
    exact (mul_le_mul_of_nonneg_right hχB (norm_nonneg a)).trans_lt hab

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
