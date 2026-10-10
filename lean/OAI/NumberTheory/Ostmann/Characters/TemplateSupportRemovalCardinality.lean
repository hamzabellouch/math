import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalSelected

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template
open SymbolicHistory
variable {ι : Type*}

theorem pivotExpressions_length_add_one (k j : ℕ) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) : (pivotExpressions k j s e t).length+1=2^j := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih =>
    simp only [pivotExpressions,List.length_cons,List.length_append]
    have hl := ih t.1.1 (childExpressions k j true e (pivotExpression k j e s t.1.1 t.1.2)) t.2.1
    have hr := ih t.1.2 (childExpressions k j false e (pivotExpression k j e s t.1.1 t.1.2)) t.2.2
    rw [pow_succ]
    omega

theorem obstructionExpressions_length_add_one (k j : ℕ) (b : Bool) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) :
    (obstructionExpressions k j b s e t).length+1=2^(j+1) := by
  simp only [obstructionExpressions,List.length_append,List.length_map]
  have h := pivotExpressions_length_add_one k j s e t
  have hb := bottomExpressions_length k j b s e t
  rw [pow_succ]
  omega

theorem selected_obstruction_card_le (k j : ℕ) (b : Bool) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j)
    (D : Finset (Expr ι)) (hD : ∀ q ∈ D, q ∈ obstructionExpressions k j b s e t) :
    D.card ≤ 2^(j+1) := by
  classical
  have hs : D ⊆ (obstructionExpressions k j b s e t).toFinset := by
    intro q hq
    exact List.mem_toFinset.mpr (hD q hq)
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  have hl := obstructionExpressions_length_add_one k j b s e t
  omega

end Ostmann.Characters.Template

end

end OAI
