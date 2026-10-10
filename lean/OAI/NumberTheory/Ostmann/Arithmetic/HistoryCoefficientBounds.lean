import OAI.NumberTheory.Ostmann.Arithmetic.HistorySymbolicCost
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySymbolicLinearity
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySymbolicNumerator

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryCoefficientBounds
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistorySymbolicState HistorySymbolicEncoding HistorySymbolicLinearity
open HistorySymbolicScope HistorySymbolicNumerator HistorySymbolicCost

variable {ι : Type*}
local instance keyDecidableEq {l : ℕ} (h : History l) : DecidableEq (Key h) := Classical.decEq _

theorem coefficientHistory_above {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (second : Bool) :
    TreeAbove (keyLevel h) h (coefficientHistory h hs second) := by
  apply encode_above
  · exact ⟨trivial,trivial,fun _ => Nat.lt_succ_self l⟩
  · intro i
    change internalLevel h i - 1 < internalLevel h i
    exact Nat.sub_lt (internalLevel_pos_le h i).1 (by omega)

theorem coefficientHistory_numerators_above {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (second : Bool) :
    TreeNumeratorsAbove (keyLevel h) h (coefficientHistory h hs second) := by
  apply encode_numerators_above
  · exact ⟨trivial,trivial,fun _ => Nat.lt_succ_self l⟩
  · intro i
    change internalLevel h i - 1 < internalLevel h i
    exact Nat.sub_lt (internalLevel_pos_le h i).1 (by omega)
  · intro i
    rfl

def rootFreeLevel {l : ℕ} (h : History l) : Key h → ℕ :=
  Sum.elim (fun _ => 0) (fun _ => l+1)

theorem coefficientHistory_rootFreeAbove {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (second : Bool) :
    TreeAbove (rootFreeLevel h) h (coefficientHistory h hs second) := by
  apply encode_above
  · exact ⟨trivial,trivial,fun _ => Nat.lt_succ_self l⟩
  · intro i
    change internalLevel h i - 1 < l+1
    have hi := (internalLevel_pos_le h i).2
    omega

def StatePolynomialFree [DecidableEq ι] (i : ι) {a : State} (e : StateExpr a ι) : Prop :=
  i ∉ e.plus.numerator.vars ∧ i ∉ e.plus.denominator.vars ∧
  i ∉ e.minus.numerator.vars ∧ i ∉ e.minus.denominator.vars

theorem above_polynomial_free [DecidableEq ι] (level : ι → ℕ) (t : ℕ)
    (i : ι) (hi : level i = 0) (e : Expr ι) (he : Above level t e) :
    i ∉ e.numerator.vars ∧ i ∉ e.denominator.vars := by
  have hn : i ∉ e.atoms := by
    intro hm
    have hlt := above_atoms e he i hm
    rw [hi] at hlt
    exact Nat.not_lt_zero t hlt
  exact ⟨fun h => hn (e.fraction_vars_subset.1 h),
    fun h => hn (e.fraction_vars_subset.2 h)⟩

def TreePolynomialFree [DecidableEq ι] (i : ι) :
    {l : ℕ} → (h : History l) → TreeExpr ι h → Prop
  | _, .leaf _, e => StatePolynomialFree i e
  | _, .node _ _ _ _ _ left right, e =>
      StatePolynomialFree i e.1 ∧ TreePolynomialFree i left e.2.1 ∧
        TreePolynomialFree i right e.2.2

theorem treeAbove_polynomial_free [DecidableEq ι] (level : ι → ℕ)
    (i : ι) (hi : level i = 0) {l : ℕ} (h : History l) (e : TreeExpr ι h)
    (he : TreeAbove level h e) : TreePolynomialFree i h e := by
  induction h with
  | leaf a =>
      exact ⟨(above_polynomial_free level 0 i hi e.plus he.1).1,
        (above_polynomial_free level 0 i hi e.plus he.1).2,
        above_polynomial_free level 0 i hi e.minus he.2.1⟩
  | @node l a p u hp hm left right ihl ihr =>
      refine ⟨?_,ihl _ he.2.1,ihr _ he.2.2⟩
      exact ⟨(above_polynomial_free level (l+1) i hi e.1.plus he.1.1).1,
        (above_polynomial_free level (l+1) i hi e.1.plus he.1.1).2,
        above_polynomial_free level (l+1) i hi e.1.minus he.1.2.1⟩

theorem coefficientHistory_no_giant_variables {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (second giant : Bool) :
    TreePolynomialFree (Sum.inl giant) h (coefficientHistory h hs second) :=
  treeAbove_polynomial_free (rootFreeLevel h) _ rfl h _
    (coefficientHistory_rootFreeAbove h hs second)

theorem coefficientHistory_cost_le {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (second : Bool) :
    TreeCostLe (2^l*(h.root.small.length+2*h.internalOccurrences.length)) h
      (coefficientHistory h hs second) := by
  have he := encode_cost_le h hs (coefficientRoot h second) (compensationExpr h)
  cases second <;>
    simpa only [coefficientHistory,stateCost,coefficientRoot,rootExpr,compensationExpr,
      Expr.atomCount,slotCost,internalCost,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      internalKey_card,smul_eq_mul,mul_one,Bool.false_eq_true,ite_false,ite_true,
      Nat.zero_add] using he

end Ostmann.Arithmetic.HistoryCoefficientBounds

end

end OAI
