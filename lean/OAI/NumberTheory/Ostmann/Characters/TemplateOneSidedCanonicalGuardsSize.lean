import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCanonicalGuardsCount

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template TemplateOneSidedBudget
attribute [local instance] Classical.propDecidable
variable {ι : Type*}

theorem maskGuards_mem_historyGuards (k : ℕ) (B V : ℕ → ℤ)
    (g : (l : ℕ) → ℤ → List (Guard (schedule k l).Slot))
    (j : ℕ) (s : ℤ) (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j)
    (q : Guard ι) (hq : q ∈ maskGuards k g j s e t) :
    q ∈ historyGuards k B V g j s e t := by
  induction j generalizing s with
  | zero => exact List.mem_append_right _ hq
  | succ j ih =>
    apply List.mem_append_right
    rcases List.mem_append.mp hq with hq | hq
    · exact List.mem_append_left _ hq
    apply List.mem_append_right
    apply List.mem_append_right
    rcases List.mem_append.mp hq with hq | hq
    · exact List.mem_append_left _ (ih _ _ _ hq)
    · exact List.mem_append_right _ (ih _ _ _ hq)

theorem sourceRangeLeafGuards_size (k : ℕ) (J : ℤ) (X Δ W : ℝ)
    (e : Expressions (ι:=ι) k 0) (M : ℕ) (he : ∀i,(e i).syntaxSize ≤ M) :
    ∀q ∈ sourceRangeLeafGuards k J X Δ W e,
      q.expression.syntaxSize ≤ (Fintype.card (schedule k 0).Slot+1)*(M+1) := by
  have hM : M ≤ (Fintype.card (schedule k 0).Slot+1)*(M+1) := by nlinarith
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · rw [windowGuardList_expression _ _ _ _ q hq]
    exact (he _).trans hM
  rcases List.mem_append.mp hq with hq | hq
  · rw [windowGuardList_expression _ _ _ _ q hq]
    exact (he _).trans hM
  · rw [windowGuardList_expression _ _ _ _ q hq]
    have hh := finiteProductExpression_syntaxSize e M he
    exact hh.trans (by nlinarith)

theorem canonicalSourceLeafGuardData_size (k : ℕ) (J : ℤ) (X Δ W : ℝ)
    (j : ℕ) (s : ℤ) :
    ∀q ∈ canonicalSourceLeafGuardData k J X Δ W j s,
      q.expression.syntaxSize ≤ 2*(Fintype.card (schedule k 0).Slot+1) := by
  cases j with
  | zero =>
    simpa only [canonicalSourceLeafGuardData,show (1:ℕ)+1=2 from rfl,Nat.mul_comm] using
      sourceRangeLeafGuards_size k J X Δ W (fun i => .atom i) 1 (fun _ => le_rfl)
  | succ j => intro q hq; exact False.elim (List.not_mem_nil hq)

theorem canonicalSourceGuardList_size (k : ℕ) (B V : ℕ → ℤ) (T : ℕ → ℝ)
    (J : ℤ) (X Δ W : ℝ) (j : ℕ) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (M : ℕ) (he : ∀i,(e i).syntaxSize ≤ M) :
    ∀q ∈ canonicalSourceGuardList k B V T J X Δ W j s e t,
      q.expression.syntaxSize ≤ recursiveSizeFactor k j *
        (2*(Fintype.card (schedule k 0).Slot+1)+1)*(M+1) := by
  let G := 2*(Fintype.card (schedule k 0).Slot+1)
  have hscale : recursiveSizeFactor k j*(M+1) ≤ recursiveSizeFactor k j*(G+1)*(M+1) := by
    exact Nat.mul_le_mul_right (M+1)
      (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (recursiveSizeFactor k j) (Nat.succ_le_succ (Nat.zero_le G)))
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · rcases List.mem_append.mp hq with hq | hq
    · have hh := historyGuards_size k j B V (fun _ _ => []) 0
        (fun _ _ _ h => False.elim (List.not_mem_nil h)) s e t M he q hq
      have hh' : q.expression.syntaxSize ≤ recursiveSizeFactor k j*(M+1) := by
        simpa only [Nat.zero_add,Nat.mul_one] using hh
      exact hh'.trans hscale
    · exact (pivotCellGuards_size k T W j s e t M he q hq).trans hscale
  · exact historyGuards_size k j B V (canonicalSourceLeafGuardData k J X Δ W) G
      (canonicalSourceLeafGuardData_size k J X Δ W) s e t M he q
      (maskGuards_mem_historyGuards k B V _ j s e t q hq)

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
