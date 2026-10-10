import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalSchwartzKernel

namespace OAI

/-!
# Seminorm bounds for the fractional Schwartz kernel

Second-derivative seminorms control the near-origin contribution of the
fractional Schwartz kernel. Growth estimates for inverse powers of distance
bound the exterior contribution in terms of the supremum seminorm.
-/

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology Set
open scoped NNReal ENNReal

theorem schwartz_second_derivative_seminorm_bound {d : ℕ} (g : 𝓢(Ambient d, ℂ)) :
    SchwartzMap.seminorm ℝ 0 0
      (fderivCLM ℝ (Ambient d) (Ambient d →L[ℝ] ℂ) (fderivCLM ℝ (Ambient d) ℂ g)) ≤
      SchwartzMap.seminorm ℝ 0 2 g := by
  apply seminorm_le_bound ℝ 0 0 _ (apply_nonneg _ _)
  intro x
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero, fderivCLM_apply]
  change ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ SchwartzMap.seminorm ℝ 0 2 g
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  exact g.norm_iteratedFDeriv_le_seminorm ℝ 2 x

theorem fractionalSchwartzKernel_integral_norm_bound {d : ℕ}
    (p : ℕ) (C : ℝ) (μ : Measure (Ambient d)) (hgrowth : GlobalUpperGrowth (p + 1) C μ)
    (g : 𝓢(Ambient d, ℂ)) (x : Ambient d) :
    (∫ h, ‖fractionalSchwartzKernel (p + 1) g x h‖ ∂μ) ≤
      4 * (C * 2 ^ (p + 1) * 2 ^ p) * SchwartzMap.seminorm ℝ 0 2 g +
        8 * (C * 2 ^ (p + 1)) * SchwartzMap.seminorm ℝ 0 0 g := by
  let M := SchwartzMap.seminorm ℝ 0 0
    (fderivCLM ℝ (Ambient d) (Ambient d →L[ℝ] ℂ) (fderivCLM ℝ (Ambient d) ℂ g))
  let N := SchwartzMap.seminorm ℝ 0 0 g
  have hM : 0 ≤ M := apply_nonneg _ _
  have hN : 0 ≤ N := apply_nonneg _ _
  have hM2 : M ≤ SchwartzMap.seminorm ℝ 0 2 g := schwartz_second_derivative_seminorm_bound g
  have hK := fractionalSchwartzKernel_integrable_of_growth p C μ hgrowth g x
  have hnearK := (inverseDistancePow_near_integrable_and_bound p C μ hgrowth 0 1 (by norm_num)).1
  have hnearB := inverseDistancePow_near_integral_bound p C μ hgrowth 0 1 (by norm_num)
  have hnear : (∫ h in ball 0 1, ‖fractionalSchwartzKernel (p + 1) g x h‖ ∂μ) ≤
      4 * (C * 2 ^ (p + 1) * 2 ^ p) * SchwartzMap.seminorm ℝ 0 2 g := by
    calc
      _ ≤ ∫ h in closedBall 0 1, ‖fractionalSchwartzKernel (p + 1) g x h‖ ∂μ :=
        integral_mono_measure (Measure.restrict_mono ball_subset_closedBall le_rfl)
          (Filter.Eventually.of_forall fun _ => norm_nonneg _) hK.norm.restrict
      _ ≤ ∫ h in closedBall 0 1, (2 * M) * inverseDistancePow p 0 h ∂μ :=
        integral_mono hK.norm.restrict (hnearK.const_mul _) (fractionalSchwartzKernel_near_bound p g x)
      _ = (2 * M) * ∫ h in closedBall 0 1, inverseDistancePow p 0 h ∂μ := integral_const_mul _ _
      _ ≤ (2 * M) * (2 * (C * 2 ^ (p + 1) * 2 ^ p * 1)) :=
        mul_le_mul_of_nonneg_left hnearB (by positivity)
      _ ≤ _ := by nlinarith [hgrowth.1, mul_nonneg hgrowth.1 (by positivity : 0 ≤ (2 : ℝ) ^ (p + 1) * 2 ^ p), hM2]
  obtain ⟨hfarK, hfarB⟩ := inverseDistancePow_closedExterior_integrable_and_bound
    (p + 1) C μ hgrowth 0 1 (by norm_num)
  have hext : (ball (0 : Ambient d) 1)ᶜ = closedExterior 0 1 := by
    ext h
    simp only [mem_compl_iff, mem_ball, closedExterior, mem_ofPred_eq, not_lt, dist_comm h 0]
  have hfar : (∫ h in (ball 0 1)ᶜ, ‖fractionalSchwartzKernel (p + 1) g x h‖ ∂μ) ≤
      8 * (C * 2 ^ (p + 1)) * SchwartzMap.seminorm ℝ 0 0 g := by
    rw [hext]
    calc
      _ ≤ ∫ h in closedExterior 0 1, (4 * N) * inverseDistancePow (p + 1 + 1) 0 h ∂μ :=
        integral_mono hK.norm.restrict (hfarK.const_mul _) (fractionalSchwartzKernel_far_bound (p + 1) g x)
      _ = (4 * N) * ∫ h in closedExterior 0 1, inverseDistancePow (p + 1 + 1) 0 h ∂μ := integral_const_mul _ _
      _ ≤ (4 * N) * (2 * (C * 2 ^ (p + 1) / 1)) := mul_le_mul_of_nonneg_left hfarB (by positivity)
      _ = _ := by dsimp [N]; ring
  rw [← integral_add_compl measurableSet_ball hK.norm]
  exact add_le_add hnear hfar

end

end RieszRectifiability

end OAI
