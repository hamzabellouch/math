import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperatorWeighted
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationBiasedKernelSumSymbolic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSelectedUniversalSymbolicFamily
open Construction Conclusion CompensationEqualityPatterns HistoryPairSourceLaws
open HistoryPairRepresentatives HistoryPairKernelReplacement HistoryBulkReferenceFrequencyFamily
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
  {outside : List ℕ} {l : ℕ} {x y : InternalSourceDraws sources seed l}
variable {origin τ : ι → ℕ} {p : Pattern τ}

def symbolicFamilyWeight
    (refs : RootReferenceFamily sources seed V outside l x y)
    (b : Block p → CommonSample sources origin)
    (representative : ∀ i : RootPresent refs,
      Block p ≃ Representative (rootLeftHistory refs i) (rootRightHistory refs i))
    (mixed : Bool) (mask : RootPresent refs → ℝ) (i : RootPresent refs) : ℂ :=
  ((mask i * ∏ q : Block p,
    symbolicKernel mixed (rootLeftHistory refs i) (rootRightHistory refs i)
      (rootLeftHistory_supported refs i) (rootRightHistory_supported refs i)
      (representative i q) (b q).val : ℝ) : ℂ)

omit [DecidableEq ι] in
theorem symbolicFamilyWeight_norm_le
    (refs : RootReferenceFamily sources seed V outside l x y)
    (b : Block p → CommonSample sources origin)
    (representative : ∀ i : RootPresent refs,
      Block p ≃ Representative (rootLeftHistory refs i) (rootRightHistory refs i))
    (mixed : Bool) (mask : RootPresent refs → ℝ)
    (hm : ∀ i, 0 ≤ mask i ∧ mask i ≤ 1) (i : RootPresent refs) :
    ‖symbolicFamilyWeight refs b representative mixed mask i‖ ≤
      ∏ q : Block p, 2 / ((b q).val : ℝ) := by
  have hK (q : Block p) := symbolicKernel_le_two_div mixed
    (rootLeftHistory refs i) (rootRightHistory refs i)
    (rootLeftHistory_supported refs i) (rootRightHistory_supported refs i)
    (representative i q) (b q).val (commonSample_prime sources origin (b q))
  have hn : 0 ≤ ∏ q : Block p,
      symbolicKernel mixed (rootLeftHistory refs i) (rootRightHistory refs i)
        (rootLeftHistory_supported refs i) (rootRightHistory_supported refs i)
        (representative i q) (b q).val :=
    Finset.prod_nonneg (fun q _ => (hK q).1)
  rw [symbolicFamilyWeight,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (hm i).1 hn)]
  exact (mul_le_of_le_one_left hn (hm i).2).trans
    (Finset.prod_le_prod₀ (fun q _ => (hK q).1) (fun q _ => (hK q).2))

omit [DecidableEq ι] in
theorem reciprocalBlockProduct_nonneg (b : Block p → CommonSample sources origin) :
    0 ≤ ∏ q : Block p, 2 / ((b q).val : ℝ) :=
  Finset.prod_nonneg (fun q _ => div_nonneg (by norm_num) (Nat.cast_nonneg _))

end Ostmann.Arithmetic.HistoryBulkSelectedUniversalSymbolicFamily

end

end OAI
