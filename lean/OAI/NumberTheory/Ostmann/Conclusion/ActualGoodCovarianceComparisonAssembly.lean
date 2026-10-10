import OAI.NumberTheory.Ostmann.Arithmetic.HistoryActualComparisonDecayArithmetic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementPlainStatement
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGoodPrincipalFinalRate
import OAI.NumberTheory.Ostmann.Conclusion.ActualComparisonProviders
import OAI.NumberTheory.Ostmann.Conclusion.ActualGoodCovarianceComparisonBasic
import OAI.NumberTheory.Ostmann.Conclusion.ActualGoodCovarianceComparisonPrincipal

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Conclusion
open Construction Arithmetic Filter HistoryBulkActualTotalReplacement
open HistoryGoodPrincipalFinalRate HistoryActualComparisonDecayArithmetic

theorem actualGoodCovarianceComparisonProvider_of_total (d : Decomposition)
    (htotal : ∀ BD Bz : ℝ, ∀ k : ℕ, 2 ≤ k →
      PlainTotalEstimate d 200 BD Bz (67*(2:ℝ)^k) k) :
    ActualGoodCovarianceComparisonProvider d := by
  intro BD Bz _hBD _hBz k hk
  let H := finalRateConstant 200 BD Bz k 67
  have hH : 0 ≤ H := (finalRateConstant_pos 200 BD Bz k (Nat.cast_nonneg 67)).le
  obtain ⟨ε,hε,hmain⟩ := exists_plainFinalAverage_budget d BD Bz H hk hH
  refine ⟨ε,hε,?_⟩
  filter_upwards [hmain,
    htotal BD Bz k hk,
    (bulkSize_tendsto_atTop (lt_of_lt_of_le (Nat.zero_lt_succ 1) hk)).eventually_ge_atTop 1]
    with L hprincipal herror hm
  intro P hP hZ E C hs a b hgood
  let spectator := harmonicPrimeSource P hP hZ
  obtain ⟨hactual,herror⟩ := herror E C hs.block_lower hs.block_upper hs.center_lower
    hs.center_upper hs.bulk_bin hs.spectator_bin spectator hs.spectator_band
  obtain ⟨hV,herror⟩ := herror k le_rfl
  obtain ⟨hV',hprincipal⟩ := hprincipal P hP hZ E C hs hactual k le_rfl
  have hm' : 1 ≤ bulkSize k L := by exact_mod_cast hm
  let z := plainOriginalAverage (l:=k) C spectator (a⁻¹*b) false
  let w := plainFinalAverage (l:=k) C spectator hactual le_rfl (a⁻¹*b) false hV
  have herr : ‖z-w‖ ≤ Real.exp (-(frequencyBudget 200 BD Bz k L k+
      67*(2:ℝ)^k*(bulkSize k L:ℝ))) := by
    simpa only [z,w,sub_eq_add_neg,neg_add,neg_mul] using (herror (a⁻¹*b) false).1
  have hpr : ‖w‖ ≤ Real.exp (-(frequencyBudget 200 BD Bz k L k+
      67*(2:ℝ)^k*(bulkSize k L:ℝ))) :=
    (hprincipal (a⁻¹*b) hgood false).trans
      (exp_final_rate_le (l:=k) 200 BD Bz k L (Nat.cast_nonneg 67) hm' le_rfl)
  apply (selectedCovariance_le_norm_relative_plainOriginal (l:=k) C spectator a b).trans
  change ‖z‖ ≤ _
  have hnorm : ‖z‖ ≤ ‖z-w‖+‖w‖ := by
    calc
      ‖z‖ = ‖(z-w)+w‖ := congrArg norm (sub_add_cancel z w).symm
      _ ≤ _ := norm_add_le _ _
  exact hnorm.trans (two_terms_exp_67_65_le k hm herr hpr)

end Ostmann.Conclusion

end

end OAI
