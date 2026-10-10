import OAI.Analysis.LipschitzHilbert.Estimates.TopDyadicDomination
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! Summing the dilation costs in the popular-top testing estimate.
The exponent three comes from the two-dimensional dilation and the
weak-L2 layer-cake estimate; degree four already makes the series summable. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace LipschitzHilbert

theorem dyadic_cubic_decay (D R A : ℝ) (hD : 4 ≤ D) (hR : 0 ≤ R) (hA : 0 ≤ A) (n : ℕ) :
    (4^D*(2^(-D))^n)*(A*(R*2^n)^3) ≤ (4^D*A*R^3)*((1:ℝ)/2)^n := by
  have hq : (2:ℝ)^(-D)*8 ≤ (1:ℝ)/2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (show -D ≤ (-4:ℝ) by linarith)
    norm_num at h
    linarith
  have heq : (4^D*(2^(-D))^n)*(A*(R*2^n)^3) =
      (4^D*A*R^3)*((2:ℝ)^(-D)*8)^n := by
    rw [mul_pow, mul_pow, show ((2:ℝ)^n)^3 = (8:ℝ)^n by rw [← pow_mul, mul_comm n, pow_mul]; norm_num]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hq n) (by positivity)

theorem top_lintegral_of_dilated_testing {ι : Type*} [Fintype ι]
    (μ : Measure (ℝ × ℝ)) (T : ι → SlopeBox) (K R D A : ℝ)
    (hK : 0 < K) (hKR : K ≤ R) (hD : 4 ≤ D) (hA : 0 ≤ A)
    (htest : ∀ n : ℕ, (∑ i, μ ((T i).radialDilation (R*2^n))) ≤
      ENNReal.ofReal (A*(R*2^n)^3)) :
    (∫⁻ z, ENNReal.ofReal (∑ i, (T i).weight K D z) ∂μ) ≤
      ENNReal.ofReal (2*4^D*A*R^3) := by
  classical
  have hD0 : 0 ≤ D := by linarith
  have hR : 0 ≤ R := (hK.trans_le hKR).le
  have hweight (i : ι) :
      (∫⁻ z, ENNReal.ofReal ((T i).weight K D z) ∂μ) ≤
        ∑' n : ℕ, ENNReal.ofReal (4^D*(2^(-D))^n) *
          μ ((T i).radialDilation (R*2^n)) := by
    calc
      _ ≤ ∫⁻ z, ∑' n : ℕ, ENNReal.ofReal (4^D*(2^(-D))^n) *
          ((T i).radialDilation (R*2^n)).indicator (fun _ => (1:ℝ≥0∞)) z ∂μ :=
        lintegral_mono ((T i).weight_le_dyadic_sum K R D hK hKR hD0)
      _ = _ := by
        rw [lintegral_tsum]
        · congr 1; funext n
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_indicator_fun_one ((T i).measurableSet_radialDilation _)]
        · intro n
          exact (measurable_const.mul (measurable_const.indicator
            ((T i).measurableSet_radialDilation _))).aemeasurable
  calc
    _ = ∑ i, ∫⁻ z, ENNReal.ofReal ((T i).weight K D z) ∂μ := by
      simp_rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => ((T i).weight_pos hK D _).le)]
      exact lintegral_finsetSum _ (fun i _ =>
        ((T i).weight_continuous K D hK).measurable.ennreal_ofReal)
    _ ≤ ∑ i, ∑' n : ℕ, ENNReal.ofReal (4^D*(2^(-D))^n) *
        μ ((T i).radialDilation (R*2^n)) := Finset.sum_le_sum fun i _ => hweight i
    _ = ∑' n : ℕ, ENNReal.ofReal (4^D*(2^(-D))^n) *
        ∑ i, μ ((T i).radialDilation (R*2^n)) := by
      rw [← tsum_fintype (L := SummationFilter.unconditional _), ENNReal.tsum_comm]
      simp only [tsum_fintype, Finset.mul_sum]
    _ ≤ ∑' n : ℕ, ENNReal.ofReal ((4^D*A*R^3)*((1:ℝ)/2)^n) := by
      apply ENNReal.tsum_le_tsum
      intro n
      calc
        _ ≤ ENNReal.ofReal (4^D*(2^(-D))^n)*ENNReal.ofReal (A*(R*2^n)^3) :=
          mul_le_mul' le_rfl (htest n)
        _ = ENNReal.ofReal ((4^D*(2^(-D))^n)*(A*(R*2^n)^3)) := by
          exact (ENNReal.ofReal_mul (by positivity)).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal (dyadic_cubic_decay D R A hD hR hA n)
    _ = ENNReal.ofReal (2*4^D*A*R^3) := by
      have hs : Summable (fun n : ℕ => ((1:ℝ)/2)^n) :=
        summable_geometric_of_lt_one (by norm_num) (by norm_num)
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (hs.mul_left _),
        tsum_mul_left, tsum_geometric_two]
      congr 1
      ring

end LipschitzHilbert

end

end OAI
