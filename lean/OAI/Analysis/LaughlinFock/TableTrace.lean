import Mathlib
import OAI.Analysis.LaughlinFock.CouplingTables
import OAI.Analysis.LaughlinFock.FastTrace

namespace OAI

/-! Table Trace. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def memoIntegerCopyPolynomial (D T r p j k : ℕ) : ℤ :=
  if r ≤ j+k then
    memoUnitCoupling r (j+k-r) j * memoUnitCoupling (D-r) (T-D) p
  else 0

theorem memoIntegerCopyPolynomial_spec {D T : ℕ} (hD : D ≤ 23) (hT : T ≤ 23)
    (r : CopyLabel D) (p j k : ℕ) (hp : p ≤ 8) (hj : j ≤ 8) (hk : k ≤ 8) :
    fastIntegerCopyPolynomial D T r.val.val p j k =
      memoIntegerCopyPolynomial D T r.val.val p j k := by
  have hr := r.val.isLt
  unfold fastIntegerCopyPolynomial memoIntegerCopyPolynomial
  split_ifs with hh
  · rw [memoUnitCoupling_spec _ _ _ (by omega) (by omega) (by omega),
      memoUnitCoupling_spec _ _ _ (by omega) (by omega) (by omega)]
  · rfl

def memoScaledFourTrace (D : ℕ) (t : Fin 8) (r s : CopyLabel D) : ℤ :=
  -(∑ b : RowEntry t.val, ∑ c : RowEntry t.val, if D ≤ rowFourLevel b c then
    certificateAlphaData t b.val.1 b.val.2 * certificateAlphaData t c.val.1 c.val.2 *
      (scaledFourFactor D t b c : ℤ) *
      memoIntegerCopyPolynomial D (rowFourLevel b c) r.val.val (rowP b) (rowJ b) (rowI c) *
      memoIntegerCopyPolynomial D (rowFourLevel b c) s.val.val (rowP c) (rowJ c) (rowI b)
    else 0)

theorem memoScaledFourTrace_spec {D : ℕ} (hD : D ≤ 23) (t : Fin 8) (r s : CopyLabel D) :
    scaledFourTrace D t r s = memoScaledFourTrace D t r s := by
  unfold scaledFourTrace memoScaledFourTrace
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  have hb := rowEntry_bounds b
  have hc := rowEntry_bounds c
  rw [memoIntegerCopyPolynomial_spec hD (rowFourLevel_le b c) r _ _ _ (by omega) hb.2.1 hc.2.2.1,
    memoIntegerCopyPolynomial_spec hD (rowFourLevel_le b c) s _ _ _ (by omega) hc.2.1 hb.2.2.1]

def memoScaledRowsFourTrace (D : ℕ) (r s : CopyLabel D) : ℤ :=
  ∑ t : Fin 8, memoScaledFourTrace D t r s

theorem integerRowsFourTrace_memo {D : ℕ} (hD : D ≤ 23) (r s : CopyLabel D) :
    integerRowsFourTrace D r s = (memoScaledRowsFourTrace D r s : ℚ) / fourCommonDenominator := by
  rw [integerRowsFourTrace_scaled]
  unfold scaledRowsFourTrace memoScaledRowsFourTrace
  simp only [memoScaledFourTrace_spec hD]

end LaughlinFock
end

end OAI
