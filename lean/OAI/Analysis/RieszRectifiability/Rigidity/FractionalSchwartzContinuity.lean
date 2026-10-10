import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalSchwartzBounds
import OAI.Analysis.RieszRectifiability.Kernel.MeanZeroSchwartzApproximation

namespace OAI

/-!
# Continuity of fractional Schwartz tests

The integral defining a fractional Schwartz test respects addition and scalar
multiplication. Uniform seminorm bounds control these tests and support their
continuity under Schwartz approximation.
-/

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology
open scoped NNReal ENNReal

theorem fractionalSchwartzTest_add (p : ℕ) (f g : 𝓢(Ambient (p + 1), ℂ))
    (x : Ambient (p + 1)) :
    fractionalSchwartzTest p (f + g) x = fractionalSchwartzTest p f x + fractionalSchwartzTest p g x := by
  have he : fractionalSchwartzKernel (p + 1) (f + g) x =
      fun h => fractionalSchwartzKernel (p + 1) f x h + fractionalSchwartzKernel (p + 1) g x h := by
    funext h
    simp only [fractionalSchwartzKernel, symmetricSecondDifference, _root_.add_apply,
      smul_add, smul_sub]
    abel
  unfold fractionalSchwartzTest
  rw [he, integral_add (fractionalSchwartzKernel_integrable p f x)
    (fractionalSchwartzKernel_integrable p g x)]
  exact smul_add (-1 / 2 : ℝ) (∫ h, fractionalSchwartzKernel (p + 1) f x h)
    (∫ h, fractionalSchwartzKernel (p + 1) g x h)

theorem fractionalSchwartzTest_smul (p : ℕ) (c : ℂ) (g : 𝓢(Ambient (p + 1), ℂ))
    (x : Ambient (p + 1)) :
    fractionalSchwartzTest p (c • g) x = c • fractionalSchwartzTest p g x := by
  have he : fractionalSchwartzKernel (p + 1) (c • g) x =
      fun h => c • fractionalSchwartzKernel (p + 1) g x h := by
    funext h
    simp only [fractionalSchwartzKernel, symmetricSecondDifference, _root_.smul_apply,
      smul_add, smul_sub, smul_comm (2 : ℝ) c, smul_comm (inverseDistancePow _ _ _) c]
  unfold fractionalSchwartzTest
  rw [he, integral_smul, smul_comm]

theorem fractionalSchwartzTest_uniform_bound (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ))
    (x : Ambient (p + 1)) :
    ‖fractionalSchwartzTest p g x‖ ≤
      4 * (((volume : Measure (Ambient (p + 1))) (ball 0 1)).toReal * 2 ^ (p + 1) * 2 ^ p) *
        SchwartzMap.seminorm ℝ 0 2 g +
      8 * (((volume : Measure (Ambient (p + 1))) (ball 0 1)).toReal * 2 ^ (p + 1)) *
        SchwartzMap.seminorm ℝ 0 0 g := by
  have hb := fractionalSchwartzKernel_integral_norm_bound p _ volume
    (volume_global_upper_growth (p + 1)) g x
  have hn := norm_integral_le_integral_norm (μ := (volume : Measure (Ambient (p + 1))))
    (fractionalSchwartzKernel (p + 1) g x)
  unfold fractionalSchwartzTest
  rw [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal]
  norm_num
  nlinarith [norm_nonneg (∫ h, fractionalSchwartzKernel (p + 1) g x h)]

theorem fractionalSchwartzTest_measurable (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ)) :
    Measurable (fractionalSchwartzTest p g) := by
  have hm : Measurable (fun q : Ambient (p + 1) × Ambient (p + 1) =>
      fractionalSchwartzKernel (p + 1) g q.1 q.2) := by
    unfold fractionalSchwartzKernel symmetricSecondDifference inverseDistancePow
    fun_prop
  unfold fractionalSchwartzTest
  simp_rw [RCLike.real_smul_eq_coe_mul]
  exact measurable_const.mul (hm.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure (Ambient (p + 1))))).measurable

def fractionalSchwartzTestCLM (p : ℕ) (x : Ambient (p + 1)) :
    𝓢(Ambient (p + 1), ℂ) →L[ℂ] ℂ := by
  apply mkCLMtoNormedSpace (fun g => fractionalSchwartzTest p g x)
    (fun f g => fractionalSchwartzTest_add p f g x)
    (fun c g => fractionalSchwartzTest_smul p c g x)
  let C := ((volume : Measure (Ambient (p + 1))) (ball 0 1)).toReal
  let A := 4 * (C * 2 ^ (p + 1) * 2 ^ p)
  let B := 8 * (C * 2 ^ (p + 1))
  let s : Finset (ℕ × ℕ) := {(0, 0), (0, 2)}
  refine ⟨s, A + B, by dsimp [A, B, C]; positivity, fun g => ?_⟩
  have h0 : SchwartzMap.seminorm ℝ 0 0 g ≤ s.sup (schwartzSeminormFamily ℂ (Ambient (p + 1)) ℂ) g := by
    exact Seminorm.le_def.mp (Finset.le_sup
      (f := schwartzSeminormFamily ℂ (Ambient (p + 1)) ℂ) (by simp [s] : (0, 0) ∈ s)) g
  have h2 : SchwartzMap.seminorm ℝ 0 2 g ≤ s.sup (schwartzSeminormFamily ℂ (Ambient (p + 1)) ℂ) g := by
    exact Seminorm.le_def.mp (Finset.le_sup
      (f := schwartzSeminormFamily ℂ (Ambient (p + 1)) ℂ) (by simp [s] : (0, 2) ∈ s)) g
  have hA : 0 ≤ A := by dsimp [A, C]; positivity
  have hB : 0 ≤ B := by dsimp [B, C]; positivity
  calc
    _ ≤ A * SchwartzMap.seminorm ℝ 0 2 g + B * SchwartzMap.seminorm ℝ 0 0 g :=
      fractionalSchwartzTest_uniform_bound p g x
    _ ≤ (A + B) * s.sup (schwartzSeminormFamily ℂ (Ambient (p + 1)) ℂ) g := by
      nlinarith [mul_le_mul_of_nonneg_left h2 hA, mul_le_mul_of_nonneg_left h0 hB]

theorem fractionalSchwartzTestCLM_apply (p : ℕ) (x : Ambient (p + 1))
    (g : 𝓢(Ambient (p + 1), ℂ)) : fractionalSchwartzTestCLM p x g = fractionalSchwartzTest p g x := rfl

theorem fractionalSchwartzTest_tendsto (p : ℕ) (G : ℕ → 𝓢(Ambient (p + 1), ℂ))
    (g : 𝓢(Ambient (p + 1), ℂ)) (ht : Tendsto G atTop (𝓝 g)) (x : Ambient (p + 1)) :
    Tendsto (fun j => fractionalSchwartzTest p (G j) x) atTop (𝓝 (fractionalSchwartzTest p g x)) :=
  (fractionalSchwartzTestCLM p x).continuous.tendsto g |>.comp ht

end

end RieszRectifiability

end OAI
