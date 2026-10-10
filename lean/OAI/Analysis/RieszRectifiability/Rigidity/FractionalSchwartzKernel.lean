import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.ClosedTailBounds
import OAI.Analysis.RieszRectifiability.Kernel.KernelNear
import OAI.Analysis.RieszRectifiability.Kernel.SchwartzSecondDifference

namespace OAI

/-!
# Integrability of fractional Schwartz kernels

Second-difference estimates control the fractional kernel near the origin, while
Schwartz bounds and inverse-distance tails control its exterior integral. Combining
the two regions gives integrability under upper growth and, in particular, for volume.
-/

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology Set
open scoped NNReal ENNReal

theorem volume_global_upper_growth (d : ℕ) :
    GlobalUpperGrowth d ((volume : Measure (Ambient d)) (ball 0 1)).toReal
      (volume : Measure (Ambient d)) := by
  refine ⟨ENNReal.toReal_nonneg, fun x r hr => ?_⟩
  rw [Measure.addHaar_ball_of_pos volume x hr]
  have hf : (volume : Measure (Ambient d)) (ball 0 1) ≠ ∞ := measure_ball_lt_top.ne
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hf]
  simp only [Ambient, finrank_euclideanSpace, Fintype.card_fin]
  exact le_of_eq (mul_comm _ _)

def fractionalSchwartzKernel {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m : ℕ) (g : Ambient d → F) (x h : Ambient d) : F :=
  inverseDistancePow (m + 1) 0 h • symmetricSecondDifference g x h

theorem fractionalSchwartzKernel_near_bound {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : ℕ) (g : 𝓢(Ambient d, F)) (x h : Ambient d) :
    ‖fractionalSchwartzKernel (p + 1) g x h‖ ≤
      (2 * SchwartzMap.seminorm ℝ 0 0
        (fderivCLM ℝ (Ambient d) (Ambient d →L[ℝ] F) (fderivCLM ℝ (Ambient d) F g))) *
          inverseDistancePow p 0 h := by
  have hb := schwartz_second_difference_quadratic_bound g x h
  rw [fractionalSchwartzKernel, norm_smul,
    Real.norm_of_nonneg (inverseDistancePow_nonneg _ _ _)]
  by_cases hh : h = 0
  · subst h
    simp only [inverseDistancePow, dist_self, zero_pow (by omega : p + 1 + 1 ≠ 0),
      inv_zero, zero_mul]
    positivity
  · have hn : ‖h‖ ≠ 0 := norm_ne_zero_iff.mpr hh
    calc
      _ ≤ inverseDistancePow (p + 1 + 1) 0 h *
          (2 * SchwartzMap.seminorm ℝ 0 0
            (fderivCLM ℝ (Ambient d) (Ambient d →L[ℝ] F) (fderivCLM ℝ (Ambient d) F g)) * ‖h‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hb (inverseDistancePow_nonneg _ _ _)
      _ = _ := by
        simp only [inverseDistancePow, dist_zero_left, pow_succ]
        field_simp

theorem fractionalSchwartzKernel_far_bound {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m : ℕ) (g : 𝓢(Ambient d, F)) (x h : Ambient d) :
    ‖fractionalSchwartzKernel m g x h‖ ≤
      (4 * SchwartzMap.seminorm ℝ 0 0 g) * inverseDistancePow (m + 1) 0 h := by
  rw [fractionalSchwartzKernel, norm_smul,
    Real.norm_of_nonneg (inverseDistancePow_nonneg _ _ _)]
  calc
    _ ≤ inverseDistancePow (m + 1) 0 h * (4 * SchwartzMap.seminorm ℝ 0 0 g) :=
      mul_le_mul_of_nonneg_left (schwartz_second_difference_uniform_bound g x h)
        (inverseDistancePow_nonneg _ _ _)
    _ = _ := mul_comm _ _

theorem fractionalSchwartzKernel_integrable_of_growth {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : ℕ) (C : ℝ) (μ : Measure (Ambient d)) (hgrowth : GlobalUpperGrowth (p + 1) C μ)
    (g : 𝓢(Ambient d, F)) (x : Ambient d) :
    Integrable (fractionalSchwartzKernel (p + 1) g x) μ := by
  have hmeas : AEStronglyMeasurable (fractionalSchwartzKernel (p + 1) g x) μ := by
    apply ((inverseDistancePow_measurable (p + 1 + 1) (0 : Ambient d)).aestronglyMeasurable.smul
      (show Continuous (symmetricSecondDifference g x) from (by
        unfold symmetricSecondDifference
        fun_prop)).aestronglyMeasurable)
  have hnear : IntegrableOn (fractionalSchwartzKernel (p + 1) g x) (closedBall 0 1) μ := by
    have hi := (inverseDistancePow_near_integrable_and_bound p C μ hgrowth 0 1 (by norm_num)).1
    apply (hi.const_mul (2 * SchwartzMap.seminorm ℝ 0 0
      (fderivCLM ℝ (Ambient d) (Ambient d →L[ℝ] F) (fderivCLM ℝ (Ambient d) F g)))).mono'
        hmeas.restrict
    exact Filter.Eventually.of_forall (fractionalSchwartzKernel_near_bound p g x)
  have hfar : IntegrableOn (fractionalSchwartzKernel (p + 1) g x) (closedExterior 0 1) μ := by
    have hi := (inverseDistancePow_closedExterior_integrable_and_bound
      (p + 1) C μ hgrowth 0 1 (by norm_num)).1
    apply (hi.const_mul (4 * SchwartzMap.seminorm ℝ 0 0 g)).mono' hmeas.restrict
    exact Filter.Eventually.of_forall (fractionalSchwartzKernel_far_bound (p + 1) g x)
  have hs : closedBall (0 : Ambient d) 1 ∪ closedExterior 0 1 = univ := by
    ext h
    simp only [mem_union, mem_closedBall, dist_zero_right, closedExterior, mem_ofPred_eq,
      dist_zero_left, mem_univ, iff_true]
    exact le_total ‖h‖ 1
  have hi := hnear.union hfar
  rw [hs] at hi
  exact integrableOn_univ.mp hi

theorem fractionalSchwartzKernel_integrable (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ))
    (x : Ambient (p + 1)) : Integrable (fractionalSchwartzKernel (p + 1) g x) :=
  fractionalSchwartzKernel_integrable_of_growth p _ volume (volume_global_upper_growth (p + 1)) g x

def fractionalSchwartzTest (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ)) (x : Ambient (p + 1)) : ℂ :=
  (-1 / 2 : ℝ) • ∫ h : Ambient (p + 1), fractionalSchwartzKernel (p + 1) g x h

end

end RieszRectifiability

end OAI
