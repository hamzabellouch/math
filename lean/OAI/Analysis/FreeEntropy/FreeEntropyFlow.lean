import OAI.Analysis.FreeEntropy.EntropyDeficit

namespace OAI

noncomputable section
open MeasureTheory Set Filter Finset
namespace FiniteEntropySeparation.Model
variable (p : ℕ) [NeZero p]
theorem reciprocal_variance_intervalIntegrable (i : Fin (p+1)) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun u => (variance p i + u)⁻¹) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.inv₀ (continuous_const.add continuous_id).continuousOn
  intro u hu
  rw [uIcc_of_le hab] at hu
  change variance p i + u ≠ 0
  exact ne_of_gt (by linarith [variance_nonneg p i, hu.1])
theorem covarianceFisher_intervalIntegrable (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (covarianceFisher p) volume a b := by
  change IntervalIntegrable (fun u => ∑ i : Fin (p+1), (variance p i + u)⁻¹) volume a b
  simpa only [Finset.sum_fn] using (IntervalIntegrable.sum univ (fun i _ => reciprocal_variance_intervalIntegrable p i a b ha hab))
theorem covarianceFisher_integral (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ u in a..b, covarianceFisher p u) =
      ∑ i : Fin (p+1), (Real.log (b + variance p i) - Real.log (a + variance p i)) := by
  unfold covarianceFisher
  rw [intervalIntegral.integral_finsetSum (fun i _ => reciprocal_variance_intervalIntegrable p i a b ha hab)]
  apply sum_congr rfl
  intro i _
  rw [intervalIntegral.integral_comp_add_left (fun u : ℝ => u⁻¹), integral_inv_of_pos
    (by linarith [variance_nonneg p i]) (by linarith [variance_nonneg p i]),
    Real.log_div (by linarith [variance_nonneg p i] : variance p i+b ≠ 0)
      (by linarith [variance_nonneg p i] : variance p i+a ≠ 0)]
  simp only [add_comm]
theorem gaussianEntropy_flow (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    gaussianEntropy p b - gaussianEntropy p a =
      (1/2 : ℝ) * ∫ u in a..b, covarianceFisher p u := by
  rw [covarianceFisher_integral p a b ha hab, sum_sub_distrib]
  unfold gaussianEntropy
  ring
theorem fisherDeficit_intervalIntegrable (hp : 2 ≤ p) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fisherDeficit p) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact (fisherDeficit_tail_integrable p hp a ha).mono_set (fun u hu => hu.1)
theorem heatFisherReal_intervalIntegrable (hp : 2 ≤ p) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (heatFisherReal p) volume a b := by
  have hh := (fisherDeficit_intervalIntegrable p hp a b ha hab).add
    (covarianceFisher_intervalIntegrable p a b ha hab)
  change IntervalIntegrable (fun x => (freeFisher (τ p) (X p x)).toReal) volume a b
  simpa only [fisherDeficit, sub_add_cancel] using hh

theorem chiStar_flow (hp : 2 ≤ p) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    chiStar (τ p) (X p b) (auxiliaryNoise p) - chiStar (τ p) (X p a) (auxiliaryNoise p) =
      (((1/2 : ℝ) * ∫ u in a..b, heatFisherReal p u : ℝ) : EReal) := by
  rw [chiStar_tail_formula p hp a ha, chiStar_tail_formula p hp b (lt_of_lt_of_le ha hab),
    ← EReal.coe_sub]
  congr 1
  have hd := intervalIntegral.integral_Ioi_sub_Ioi (fisherDeficit_tail_integrable p hp a ha) hab
  have hg := gaussianEntropy_flow p a b ha hab
  have hh : (∫ u in a..b, heatFisherReal p u) =
      (∫ u in a..b, fisherDeficit p u) + (∫ u in a..b, covarianceFisher p u) := by
    rw [← intervalIntegral.integral_add (fisherDeficit_intervalIntegrable p hp a b ha hab)
      (covarianceFisher_intervalIntegrable p a b ha hab)]
    apply intervalIntegral.integral_congr
    intro u hu
    simp only [fisherDeficit, heatFisherReal, sub_add_cancel]
  rw [hh]
  linarith
end FiniteEntropySeparation.Model

end

end OAI
