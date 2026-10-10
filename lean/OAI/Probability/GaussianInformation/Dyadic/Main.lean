import Mathlib
import OAI.Probability.GaussianInformation.Dyadic.History

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace RepeatedLocalization
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem repeated_localization : MainStatement := by
  refine ⟨1/2,by norm_num,32,?_⟩
  intro C₀ hC₀
  let A := blockInformationConstant+C₀
  let K := 2*Real.log 2+1
  let D := A+K
  let C := 16*D
  have hA : 0 < A := add_pos blockInformationConstant_pos hC₀
  have hK : 0 < K := by dsimp [K]; positivity
  have hD : 0 < D := add_pos hA hK
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro n N t hn hN rules halphabet
  have hn0 : 0 < n := by omega
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  let L := A*(n+1)
  have hc : UniformBlockCost n N L := actual_uniform_blockCost hn hN halphabet
  obtain ⟨s,f,hf,hs,⟨R⟩⟩ := history_analysis_realized hn0 rules L hc
  have hi := s.information_of_potential (show 8 ≤ n by omega) hs
  have hLK : L+2*Real.log 2+1 ≤ D*(n+1) := by
    dsimp [L,D,K]
    have hnnonneg : (0:ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_nonneg hK.le hnnonneg]
  have hinfo : s.information ≤ 4*(t:ℝ)*D*(n+1) := by
    have H := mul_le_mul_of_nonneg_left hLK (by positivity : 0 ≤ 4*(t:ℝ))
    nlinarith
  have hDt : 0 ≤ D*(t:ℝ) := mul_nonneg hD.le (Nat.cast_nonneg t)
  have hfinal : s.information ≤ C*(n+1)*t := by
    apply hinfo.trans
    dsimp [C]
    nlinarith [mul_nonneg hDt (show 0 ≤ (n:ℝ)+1 by positivity)]
  refine ⟨R.Q,R.valid,?_,?_⟩
  · exact (R.information_le hn0 rules hf).trans (ENNReal.ofReal_le_ofReal hfinal)
  · rw [R.level_eq hn0 rules hf]
    have hhalf : (1/2:ℝ) ≤ Real.log 2 := by
      have H := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 2 by norm_num)
      norm_num at H ⊢
      exact H
    have hd := s.depth_nonneg
    have hl := s.information_lower hn0
    have hsmall : (n:ℝ)/2*s.depth ≤ s.information := by
      have H := mul_le_mul_of_nonneg_right hhalf (mul_nonneg (Nat.cast_nonneg n) hd)
      nlinarith
    apply le_of_mul_le_mul_left (a := (n:ℝ)/2) (a0 := by positivity)
    calc
      (n:ℝ)/2*s.depth ≤ s.information := hsmall
      _ ≤ 4*(t:ℝ)*D*(n+1) := hinfo
      _ ≤ (n:ℝ)/2*(C*t) := by
        dsimp [C]
        nlinarith [mul_nonneg hDt (sub_nonneg.mpr hnR)]
end RepeatedLocalization

end OAI
