import OAI.Analysis.LipschitzHilbert.Estimates.SlopeBoxMask
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace OAI

/-! Dyadic dilation domination for the actual decaying top weights. The
base dilation may be larger than the weight radius, as required when the
popular-rectangle argument first clips to the localization strip. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert
namespace SlopeBox

def radialDilation (T : SlopeBox) (R : ℝ) : Set (ℝ × ℝ) := {z | T.radius z ≤ R}

theorem measurableSet_radialDilation (T : SlopeBox) (R : ℝ) :
    MeasurableSet (T.radialDilation R) := by
  apply measurableSet_le _ measurable_const
  unfold radius horizontal transverse
  fun_prop

theorem exists_dyadic_weight_bound (T : SlopeBox) (K R D : ℝ)
    (hK : 0 < K) (hKR : K ≤ R) (hD : 0 ≤ D) (z : ℝ × ℝ) :
    ∃ n : ℕ, z ∈ T.radialDilation (R*2^n) ∧
      T.weight K D z ≤ 4^D*(2^(-D))^n := by
  have hR : 0 < R := hK.trans_le hKR
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hfour : (4 : ℝ)^D = (2 : ℝ)^D*(2:ℝ)^D := by
    rw [← Real.mul_rpow htwo.le htwo.le]
    norm_num
  by_cases hz : T.radius z < R
  · refine ⟨0, by simpa [radialDilation] using hz.le, ?_⟩
    simp only [pow_zero, mul_one]
    have hw : T.weight K D z ≤ (2:ℝ)^D := by
      unfold weight
      calc
        _ ≤ (2:ℝ)^D * 1 := mul_le_mul_of_nonneg_left
          (Real.rpow_le_one_of_one_le_of_nonpos (by
            exact le_add_of_nonneg_right (div_nonneg (T.radius_nonnegative z) hK.le)) (by linarith)) (by positivity)
        _ = _ := mul_one _
    apply hw.trans
    rw [hfour]
    exact le_mul_of_one_le_right (by positivity)
      (Real.one_le_rpow (by norm_num) hD)
  · have hratio : 1 ≤ T.radius z/R := (le_div_iff₀ hR).mpr (by simpa using le_of_not_gt hz)
    obtain ⟨n, hn, hn1⟩ := exists_nat_pow_near hratio (by norm_num : (1:ℝ)<2)
    refine ⟨n+1, ?_, ?_⟩
    · exact (div_lt_iff₀ hR).mp hn1 |>.le.trans_eq (mul_comm _ _)
    · have hlo : (2:ℝ)^n ≤ 1+T.radius z/K := by
        have hnon := T.radius_nonnegative z
        have hdiv : T.radius z/R ≤ T.radius z/K :=
          div_le_div_of_nonneg_left hnon hK hKR
        linarith
      have hpow := Real.rpow_le_rpow_of_nonpos (by positivity : (0:ℝ)<2^n) hlo
        (by linarith : -D ≤ 0)
      calc
        T.weight K D z ≤ (2:ℝ)^D*((2:ℝ)^n)^(-D) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = (2:ℝ)^D*(2^(-D))^n := by
          rw [← Real.rpow_natCast_mul htwo.le, mul_comm (n:ℝ), Real.rpow_mul_natCast htwo.le]
        _ = 4^D*(2^(-D))^(n+1) := by
          rw [hfour, pow_succ]
          have hc : (2:ℝ)^D*2^(-D) = 1 := by
            rw [← Real.rpow_add htwo]; simp
          symm
          calc
            _ = ((2:ℝ)^D*2^(-D))*((2:ℝ)^D*(2^(-D))^n) := by ring
            _ = _ := by rw [hc, one_mul]

theorem weight_le_dyadic_sum (T : SlopeBox) (K R D : ℝ)
    (hK : 0 < K) (hKR : K ≤ R) (hD : 0 ≤ D) (z : ℝ × ℝ) :
    ENNReal.ofReal (T.weight K D z) ≤
      ∑' n : ℕ, ENNReal.ofReal (4^D*(2^(-D))^n) *
        (T.radialDilation (R*2^n)).indicator (fun _ => (1:ℝ≥0∞)) z := by
  obtain ⟨n, hn, hweight⟩ := T.exists_dyadic_weight_bound K R D hK hKR hD z
  exact (ENNReal.ofReal_le_ofReal hweight).trans (by
    simpa only [indicator_of_mem hn, mul_one] using
      (ENNReal.le_tsum (f := fun m : ℕ => ENNReal.ofReal (4^D*(2^(-D))^m) *
          (T.radialDilation (R*2^m)).indicator (fun _ => (1:ℝ≥0∞)) z) n :
        ENNReal.ofReal (4^D*(2^(-D))^n) *
          (T.radialDilation (R*2^n)).indicator (fun _ => (1:ℝ≥0∞)) z ≤ _))

end SlopeBox
end LipschitzHilbert

end

end OAI
