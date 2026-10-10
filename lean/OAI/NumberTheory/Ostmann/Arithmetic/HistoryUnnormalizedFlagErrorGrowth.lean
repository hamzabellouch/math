import OAI.NumberTheory.Ostmann.Arithmetic.HistoryUnnormalizedFlagErrorSelected

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryUnnormalizedFlagError

lemma commonLogBudget_mono {T U L : ℝ} (hTU : T ≤ U) :
    commonLogBudget T L ≤ commonLogBudget U L :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hTU (sq_nonneg _)) (Real.exp_nonneg _)

lemma linear_le_commonLogBudget {T L : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) :
    T*(L+1) ≤ commonLogBudget T L := by
  have he : 1 ≤ Real.exp ((11/10000:ℝ)*L) := Real.one_le_exp (by positivity)
  have hs : L+1 ≤ (L+1)^2 := by nlinarith
  exact (mul_le_mul_of_nonneg_left hs hT).trans
    (le_mul_of_one_le_right (mul_nonneg hT (sq_nonneg _)) he)

end Ostmann.Arithmetic.HistoryUnnormalizedFlagError

end

end OAI
