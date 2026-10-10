import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairVariableBAverageCRT
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairVariableBAverageLoss

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryPairVariableBAverage
open Construction HistoryPairPattern HistoryPairRows HistoryPairRepresentatives
open HistoryPairSquareProbability HistoryPairKernelReplacement HistoryCRTIntegration
open HistoryBulkReferenceTests ResidueHaar
variable {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}

theorem unit_B_averageAt_probability_loss (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (v : PairKey h k→ℤ)
    (had : HistoryRepresentativeSourceSeparation.PairAdmissible h k outside)
    (hrow : ∀r : Representative h k,∀i : Fiber h k r,
      (actualLeftAt h k hs ks v r i:ZMod (prime h k r))≠0 ∨
      (actualRightAt h k hs ks v r i:ZMod (prime h k r))≠0)
    [NeZero (representativeModulus h k)] :
    0 ≤ (∏r : Representative h k,actualProbability false h k hs ks r (prime h k r) v)-(average (fun z : UnitPair (representativeModulus h k) => primeResidueIndicatorAt h k hs ks v (z.1,z.2))).re ∧
    (∏r : Representative h k,actualProbability false h k hs ks r (prime h k r) v)-(average (fun z : UnitPair (representativeModulus h k) => primeResidueIndicatorAt h k hs ks v (z.1,z.2))).re ≤ (∑i : Occurrences h k,(1:ℝ)/(slot h k i).value)*(∏r : Representative h k,actualProbability false h k hs ks r (prime h k r) v) := by
  rw [unit_B_averageAt_eq_product h k hs ks v had,← Complex.ofReal_prod,Complex.ofReal_re]
  exact unit_square_product_lossAt h k hs ks v hrow

theorem unit_B_averageAt_probability_error (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (v : PairKey h k→ℤ)
    (had : HistoryRepresentativeSourceSeparation.PairAdmissible h k outside)
    (hrow : ∀r : Representative h k,∀i : Fiber h k r,
      (actualLeftAt h k hs ks v r i:ZMod (prime h k r))≠0 ∨
      (actualRightAt h k hs ks v r i:ZMod (prime h k r))≠0)
    [NeZero (representativeModulus h k)] :
    ‖(average (fun z : UnitPair (representativeModulus h k) => primeResidueIndicatorAt h k hs ks v (z.1,z.2)))-((∏r : Representative h k,actualProbability false h k hs ks r (prime h k r) v):ℝ)‖ ≤ (∑i : Occurrences h k,(1:ℝ)/(slot h k i).value)*(∏r : Representative h k,actualProbability false h k hs ks r (prime h k r) v) := by
  have hh := unit_square_product_lossAt h k hs ks v hrow
  rw [unit_B_averageAt_eq_product h k hs ks v had,← Complex.ofReal_prod,
    ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_nonpos (by linarith :
    (∏r : Representative h k,actualUnitSquareProbabilityAt h k hs ks v r)-(∏r : Representative h k,actualProbability false h k hs ks r (prime h k r) v) ≤ 0)]
  linarith

theorem mixed_B_averageAt_probability_loss (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (v : PairKey h k→ℤ)
    (had : HistoryRepresentativeSourceSeparation.PairAdmissible h k outside)
    (hrow : ∀r : Representative h k,∀i : Fiber h k r,
      (actualLeftAt h k hs ks v r i:ZMod (prime h k r))≠0 ∨
      (actualRightAt h k hs ks v r i:ZMod (prime h k r))≠0)
    [NeZero (representativeModulus h k)] :
    0 ≤ (∏r : Representative h k,actualProbability true h k hs ks r (prime h k r) v)-(average (fun z : MixedPair (representativeModulus h k) => primeResidueIndicatorAt h k hs ks v (z.1,z.2))).re ∧
    (∏r : Representative h k,actualProbability true h k hs ks r (prime h k r) v)-(average (fun z : MixedPair (representativeModulus h k) => primeResidueIndicatorAt h k hs ks v (z.1,z.2))).re ≤ (∑i : Occurrences h k,(1:ℝ)/(slot h k i).value)*(∏r : Representative h k,actualProbability true h k hs ks r (prime h k r) v) := by
  rw [mixed_B_averageAt_eq_product h k hs ks v had,← Complex.ofReal_prod,Complex.ofReal_re]
  exact mixed_square_product_lossAt h k hs ks v hrow

theorem mixed_B_averageAt_probability_error (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (v : PairKey h k→ℤ)
    (had : HistoryRepresentativeSourceSeparation.PairAdmissible h k outside)
    (hrow : ∀r : Representative h k,∀i : Fiber h k r,
      (actualLeftAt h k hs ks v r i:ZMod (prime h k r))≠0 ∨
      (actualRightAt h k hs ks v r i:ZMod (prime h k r))≠0)
    [NeZero (representativeModulus h k)] :
    ‖(average (fun z : MixedPair (representativeModulus h k) => primeResidueIndicatorAt h k hs ks v (z.1,z.2)))-((∏r : Representative h k,actualProbability true h k hs ks r (prime h k r) v):ℝ)‖ ≤ (∑i : Occurrences h k,(1:ℝ)/(slot h k i).value)*(∏r : Representative h k,actualProbability true h k hs ks r (prime h k r) v) := by
  have hh := mixed_square_product_lossAt h k hs ks v hrow
  rw [mixed_B_averageAt_eq_product h k hs ks v had,← Complex.ofReal_prod,
    ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_nonpos (by linarith :
    (∏r : Representative h k,actualMixedSquareProbabilityAt h k hs ks v r)-(∏r : Representative h k,actualProbability true h k hs ks r (prime h k r) v) ≤ 0)]
  linarith

end Ostmann.Arithmetic.HistoryPairVariableBAverage

end

end OAI
