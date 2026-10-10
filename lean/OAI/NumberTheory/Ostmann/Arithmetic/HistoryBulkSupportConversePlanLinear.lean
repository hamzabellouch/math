import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportRowsCoefficients

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConversePlan
open Construction Construction.CanonicalOccurrenceTransport
open Characters.RationalHistory

variable {ι : Type}

def CodeLinear (x : ι → ℚ) (X Y : ℚ) (e c d : StateCode ι) : Prop :=
  e.plus.rationalEval x = c.plus.rationalEval x * X + d.plus.rationalEval x * Y ∧
  e.minus.rationalEval x = c.minus.rationalEval x * X + d.minus.rationalEval x * Y ∧
  c.small = e.small ∧ d.small = e.small

theorem fixedNodeNumerator_linear (x : ι → ℚ) (X Y : ℚ)
    (v w : ℤ) (n : ℕ) (split : List ℕ) (e c d : StateCode ι)
    (he : CodeLinear x X Y e c d) :
    (fixedNodeNumerator v w n split e).rationalEval x =
      (fixedNodeNumerator v w n split c).rationalEval x * X +
      (fixedNodeNumerator v w n split d).rationalEval x * Y := by
  simp only [fixedNodeNumerator,HistorySymbolicNumerator.numeratorExpr,
    Expr.rationalEval,he.2.2.1,he.2.2.2]
  rw [he.1,he.2.1]
  ring

theorem pivot_linear (x : ι → ℚ) (X Y : ℚ)
    (s v w : ℤ) (n : ℕ) (split : List ℕ) (u : List (Expr ι))
    (e c d : StateCode ι) (he : CodeLinear x X Y e c d) :
    (HistorySymbolicStep.pivot s v w e.plus e.minus u
      ((select (.fixed 0) split e.small).take n)
      ((select (.fixed 0) split e.small).drop n)).rationalEval x =
    (HistorySymbolicStep.pivot s v w c.plus c.minus u
      ((select (.fixed 0) split c.small).take n)
      ((select (.fixed 0) split c.small).drop n)).rationalEval x * X +
    (HistorySymbolicStep.pivot s v w d.plus d.minus u
      ((select (.fixed 0) split d.small).take n)
      ((select (.fixed 0) split d.small).drop n)).rationalEval x * Y := by
  simp only [HistorySymbolicStep.pivot_eval,he.2.2.1,he.2.2.2]
  rw [he.1,he.2.1]
  simp only [div_eq_mul_inv]
  ring

def TreeCodeLinear (x : ι → ℚ) (X Y : ℚ) :
    {l : ℕ} → TreeCode ι l → TreeCode ι l → TreeCode ι l → Prop
  | 0,e,c,d => CodeLinear x X Y e c d
  | _+1,e,c,d => CodeLinear x X Y e.1 c.1 d.1 ∧
      TreeCodeLinear x X Y e.2.1 c.2.1 d.2.1 ∧
      TreeCodeLinear x X Y e.2.2 c.2.2 d.2.2

theorem execute_linear {l : ℕ} (p : Plan l) (e c d : StateCode ι)
    (comp : CompensationCode ι l) (x : ι → ℚ) (X Y : ℚ)
    (he : CodeLinear x X Y e c d) :
    TreeCodeLinear x X Y (execute p e comp) (execute p c comp) (execute p d comp) := by
  induction p generalizing e c d with
  | leaf s => exact he
  | node s v w n split lo ro left right ihl ihr =>
    refine ⟨he,ihl _ _ _ comp.2.1 ?_,ihr _ _ _ comp.2.2 ?_⟩
    · refine ⟨pivot_linear x X Y s v w n split comp.1 e c d he,he.1,?_,?_⟩ <;>
        simp only [he.2.2.1,he.2.2.2]
    · refine ⟨pivot_linear x X Y s v w n split comp.1 e c d he,he.2.1,?_,?_⟩ <;>
        simp only [he.2.2.1,he.2.2.2]

theorem fixedRows_linear (seed : List SourceSlot) {l : ℕ} (p : Plan l)
    (e c d : TreeCode ι l) (x : ι → ℚ) (X Y : ℚ)
    (he : TreeCodeLinear x X Y e c d) (i : Internal seed l) :
    (fixedRows seed p e e i).1.rationalEval x =
      (fixedRows seed p c d i).1.rationalEval x * X +
      (fixedRows seed p c d i).2.rationalEval x * Y := by
  induction p with
  | leaf s => exact Empty.elim i
  | node s v w n split lo ro left right ihl ihr =>
    rcases i with i | i | i
    · exact fixedNodeNumerator_linear x X Y v w n split e.1 c.1 d.1 he.1
    · exact ihl e.2.1 c.2.1 d.2.1 he.2.1 i
    · exact ihr e.2.2 c.2.2 d.2.2 he.2.2 i

theorem fixedRows_execute_root_linear (seed : List SourceSlot) {l : ℕ}
    (p : Plan l) (x : Coordinate seed l → ℚ) (i : Internal seed l) :
    (fixedRows seed p
      (execute p (fixedRootCode seed l)
        (fixedCompensationCode seed l (fun j => .atom (.inr (.inr j)))))
      (execute p (fixedRootCode seed l)
        (fixedCompensationCode seed l (fun j => .atom (.inr (.inr j))))) i).1.rationalEval x =
    (fixedCanonicalRows seed p i).1.rationalEval x * x (.inl false) +
      (fixedCanonicalRows seed p i).2.rationalEval x * x (.inl true) := by
  apply fixedRows_linear
  apply execute_linear
  simp [CodeLinear,fixedRootCode,fixedCoefficientRootCode,Expr.rationalEval]

end Ostmann.Arithmetic.HistoryBulkSupportConversePlan

end

end OAI
