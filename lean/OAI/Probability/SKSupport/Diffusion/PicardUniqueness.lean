import Mathlib
import OAI.Probability.SKSupport.Diffusion.PicardDiffusion

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.BoundedLipschitzDrift

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
variable (b : BoundedLipschitzDrift)

lemma correction_unique_on (ℱ : Filtration ℝ≥0 mΩ) {B Z : ℝ≥0 → Ω → ℝ}
    (hB : IsProgressive ℱ B) (hZ : IsProgressive ℱ Z) (T : ℝ≥0) (ω : Ω)
    (hfix : ∀ t ≤ T, Z t ω = timePrimitive (b.action B Z) t ω) :
    ∀ t ≤ T, b.correction B t ω = Z t ω := by
  have hbase (t : ℝ≥0) (ht : t ≤ T) :
      |b.correction B t ω-Z t ω| ≤ 2*(b.bound:ℝ)*Real.exp (b.rate*t) := by
    have hzb : |Z t ω| ≤ (b.bound:ℝ)*(t:ℝ) := by
      rw [hfix t ht]
      exact timePrimitive_bound ℱ (b.action_progressive ℱ hB hZ) (b.action_bound _ _) _ _
    have htt : (t:ℝ) ≤ Real.exp (b.rate*t) := by
      have hh : (t:ℝ) ≤ b.rate*t := by nlinarith [b.one_le_rate,t.coe_nonneg]
      linarith [Real.add_one_le_exp (b.rate*t)]
    apply (abs_sub _ _).trans
    nlinarith [b.correction_bound ℱ hB t ω,
      mul_le_mul_of_nonneg_left htt b.bound.coe_nonneg]
  have hest (n : ℕ) (t : ℝ≥0) (ht : t ≤ T) :
      |b.correction B t ω-Z t ω| ≤ 2*(b.bound:ℝ)*(1/2:ℝ)^n*Real.exp (b.rate*t) := by
    induction n generalizing t with
    | zero => simpa only [pow_zero,mul_one] using hbase t ht
    | succ n hn =>
      rw [b.correction_eq_integral ℱ hB t ω,hfix t ht]
      have hh := b.timePrimitive_action_sub_estimate ℱ hB (b.correction_progressive ℱ hB) hZ
        (show 0 ≤ 2*(b.bound:ℝ)*(1/2:ℝ)^n by positivity) t ω (fun s hs => hn s (hs.trans ht))
      convert hh using 1
      rw [pow_succ]
      ring
  intro t ht
  have hh : Tendsto (fun n : ℕ => 2*(b.bound:ℝ)*(1/2:ℝ)^n*Real.exp (b.rate*t)) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul] using
      (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one
        (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num : (1/2:ℝ)<1))
        (a := 2*(b.bound:ℝ))).mul_const (Real.exp (b.rate*t))
  have hz : |b.correction B t ω-Z t ω| ≤ 0 :=
    ge_of_tendsto hh (Eventually.of_forall (fun n => hest n t ht))
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hz (abs_nonneg _)))

lemma solution_eq_of_agree (b' : BoundedLipschitzDrift) (ℱ : Filtration ℝ≥0 mΩ)
    {B : ℝ≥0 → Ω → ℝ} (hB : IsProgressive ℱ B) (T : ℝ≥0)
    (he : ∀ t : ℝ≥0, t ≤ T → ∀ x, b.f t x = b'.f t x) (t : ℝ≥0) (ht : t ≤ T) (ω : Ω) :
    b.solution B t ω = b'.solution B t ω := by
  have hu := b.correction_unique_on ℱ hB (b'.correction_progressive ℱ hB) T ω
  apply congrArg (B t ω+ ·)
  apply hu _ t ht
  intro s hs
  rw [b'.correction_eq_integral ℱ hB s ω]
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le s.coe_nonneg] at hr
  exact (he (Real.toNNReal r) ((Real.toNNReal_le_iff_le_coe.mpr hr.2).trans hs) _).symm

end ZeroTemperatureSK.BoundedLipschitzDrift

end
end

end OAI
