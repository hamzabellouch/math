import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairedFrequencyAverageBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairedFrequencyAverageData

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairedFrequencyAverage
open Characters FrequencyExposure FrequencyTreeSum BinaryExposure
open HistorySignedResidueFactorization

def localGuardedAverage (S : List Bool → Finset (ℤ × ℤ)) {l : ℕ} {p : List Bool}
    (x : Assignment S l p) (Q : ℕ) [NeZero Q] (hx : LabelsDivide S Q x)
    (H : Type) (a : ∀q,Coefficients H (localData S Q x hx q))
    (left right : List Bool → H → (ZMod Q)ˣ → (ZMod Q)ˣ → H) (h : H)
    (guard : BinaryHaar.Leaves (ZMod Q)ˣ l → Prop) : ℝ :=
  avg (fun z : BinaryHaar.Leaves (ZMod Q)ˣ l =>
    ‖guardIndicator (guard z ∧ leafAdmissible (constraint (localData S Q x hx) a)
      (update false left) (update true right) l ([],h) z)‖)

theorem localGuardedAverage_le_weight {ε : ℝ} {C : NNReal}
    (hcount : PairedFrequencyActualBudget.LeafCountConstant ε C)
    (S : List Bool → Finset (ℤ × ℤ)) {l : ℕ} {p : List Bool}
    (x : Assignment S l p) (Q : ℕ) [NeZero Q] (hx : LabelsDivide S Q x)
    (H : Type) (a : ∀q,Coefficients H (localData S Q x hx q))
    (left right : List Bool → H → (ZMod Q)ˣ → (ZMod Q)ˣ → H) (h : H)
    (guard : BinaryHaar.Leaves (ZMod Q)ˣ l → Prop) :
    localGuardedAverage S x Q hx H a left right h guard ≤
      weight S (PairedFrequencyTreeSum.factor (C:ℝ) ε) x :=
  (guarded_leaf_average_le hcount Q H (localData S Q x hx) a left right l [] h guard).trans_eq
    (localData_budget_eq_weight S Q C ε x hx)

theorem sum_localGuardedAverage_le_total {ε : ℝ} {C : NNReal}
    (hcount : PairedFrequencyActualBudget.LeafCountConstant ε C)
    (S : List Bool → Finset (ℤ × ℤ)) (l : ℕ) (p : List Bool)
    (Q : Assignment S l p → ℕ) [∀x,NeZero (Q x)]
    (hx : ∀x,LabelsDivide S (Q x) x)
    (H : Assignment S l p → Type)
    (a : ∀x q,Coefficients (H x) (localData S (Q x) x (hx x) q))
    (left right : ∀x,List Bool → H x → (ZMod (Q x))ˣ → (ZMod (Q x))ˣ → H x)
    (h : ∀x,H x) (guard : ∀x,BinaryHaar.Leaves (ZMod (Q x))ˣ l → Prop) :
    (∑x : Assignment S l p,
      localGuardedAverage S x (Q x) (hx x) (H x) (a x) (left x) (right x) (h x) (guard x)) ≤
      total S (PairedFrequencyTreeSum.factor (C:ℝ) ε) l p := by
  apply Finset.sum_le_sum
  intro x _
  exact localGuardedAverage_le_weight hcount S x (Q x) (hx x)
    (H x) (a x) (left x) (right x) (h x) (guard x)

end Ostmann.Arithmetic.HistoryPairedFrequencyAverage

end

end OAI
