import OAI.NumberTheory.Ostmann.Arithmetic.LinearReversal
import OAI.NumberTheory.Ostmann.Construction.History

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryLinearization
open Construction

def pivotRow (a : State) (u hp hm : List SmallSlot) (v w : ℤ) : ℚ × ℚ :=
  (-(w:ℚ)*((hp.map SmallSlot.value).prod:ℚ) /
      ((a.frequency:ℚ)*((u.map SmallSlot.value).prod:ℚ)),
    (v:ℚ)*((hm.map SmallSlot.value).prod:ℚ) /
      ((a.frequency:ℚ)*((u.map SmallSlot.value).prod:ℚ)))

theorem supported_pivot_linear {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside) :
    (p:ℚ) = (pivotRow a u hp hm left.root.frequency right.root.frequency).1 * a.giantPlus +
      (pivotRow a u hp hm left.root.frequency right.root.frequency).2 * a.giantMinus := by
  have hs0 : (a.frequency:ℚ) ≠ 0 := by
    exact_mod_cast History.supported_root_frequency_ne_zero hs
  have hu0 : ((u.map SmallSlot.value).prod:ℚ) ≠ 0 := by
    exact_mod_cast (History.supported_compensation_product_pos hs).ne'
  have heq := History.supported_reversal hs
  unfold Arithmetic.reversalNumerator at heq
  have heq' : (left.root.frequency:ℚ)*
      ((a.giantMinus:ℚ)*((hm.map SmallSlot.value).prod:ℚ)) -
      (right.root.frequency:ℚ)*((a.giantPlus:ℚ)*((hp.map SmallSlot.value).prod:ℚ)) =
      (a.frequency:ℚ)*((u.map SmallSlot.value).prod:ℚ)*(p:ℚ) := by
    have hc := congrArg (fun z : ℤ => (z:ℚ)) heq
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_mul] using hc
  exact LinearReversal.pivot_linear hs0 hu0 heq'

end Ostmann.Arithmetic.HistoryLinearization

end

end OAI
