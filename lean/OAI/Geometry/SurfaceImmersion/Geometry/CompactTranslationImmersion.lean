import OAI.Geometry.SurfaceImmersion.Geometry.CompactTranslationStability
import OAI.Geometry.SurfaceImmersion.Geometry.C1ImmersionJets

namespace OAI

/-! Small scalar-weighted translations preserve immersion on compact
coordinate domains. -/
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
local instance injectiveScalarNormed : NormedAddCommGroup (Base →L[ℝ] ℝ) := inferInstance
local instance injectiveScalarSpace : NormedSpace ℝ (Base →L[ℝ] ℝ) := inferInstance

theorem compact_translation_immersion {f : Base → ProjectionTarget 3} {χ : Base → ℝ}
    (hf : ContDiff ℝ ∞ f) (hχ : ContDiff ℝ ∞ χ)
    {K : Set Base} (hK : IsCompact K)
    (hI : ∀ x ∈ K, Function.Injective (fderiv ℝ f x)) :
    ∃ δ > 0, ∀ a : ProjectionTarget 3, ‖a‖ < δ → ∀ x ∈ K,
      Function.Injective (fderiv ℝ (fun y => f y+χ y • a) x) := by
  have hD : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  obtain ⟨ε,hε,hstable⟩ := compact_injective_stability (hK.image hD)
    (by rintro L ⟨x,hx,rfl⟩; exact hI x hx)
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn (hχ.continuous_fderiv (by simp)).continuousOn
  let B := max M 0+1
  have hB : 0 < B := by dsimp [B]; linarith [le_max_right M 0]
  refine ⟨ε/B,div_pos hε hB,?_⟩
  intro a ha x hx
  apply hstable (fderiv ℝ f x) ⟨x,hx,rfl⟩
  have hd := ((hf.differentiable (by simp) x).hasFDerivAt.add
    ((hχ.differentiable (by simp) x).hasFDerivAt.smul_const a)).fderiv
  change ‖fderiv ℝ (f + fun y => χ y • a) x-fderiv ℝ f x‖ < ε
  rw [hd,add_sub_cancel_left,ContinuousLinearMap.norm_smulRight_apply]
  have hbound : ‖fderiv ℝ χ x‖ ≤ B := (hM x hx).trans (by dsimp [B]; linarith [le_max_left M 0])
  calc
    _ ≤ B*‖a‖ := mul_le_mul_of_nonneg_right hbound (norm_nonneg a)
    _ < ε := by simpa only [mul_comm] using (lt_div_iff₀ hB).mp ha

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
