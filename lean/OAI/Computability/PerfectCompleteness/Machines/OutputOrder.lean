import Mathlib.Data.List.OfFn
import OAI.Computability.PerfectCompleteness.Machines.TransitionTemplate

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.OutputOrder

open StatementCircuit

variable {K : Type} {Γ : K → Type} {Λ σ : Type}

private theorem unindex_label (indexing : ConfigIndex.Indexing Γ Λ σ) (S : Nat)
    (label : Fin indexing.labelCount) (j : Fin (indexing.width S))
    (hj : j.val = label.val) :
    (indexing.configIndexEquiv S).symm j =
      (Sum.inl (indexing.labels.symm label) : ConfigBit Γ Λ σ S) := by
  apply (indexing.configIndexEquiv S).injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  simpa only [ConfigIndex.Indexing.configIndex_label, Equiv.apply_symm_apply] using hj

private theorem unindex_state (indexing : ConfigIndex.Indexing Γ Λ σ) (S : Nat)
    (state : Fin indexing.stateCount) (j : Fin (indexing.width S))
    (hj : j.val = indexing.labelCount + state.val) :
    (indexing.configIndexEquiv S).symm j =
      (Sum.inr (Sum.inl (indexing.states.symm state)) : ConfigBit Γ Λ σ S) := by
  apply (indexing.configIndexEquiv S).injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  simpa only [ConfigIndex.Indexing.configIndex_state, Equiv.apply_symm_apply] using hj

private theorem unindex_cell (indexing : ConfigIndex.Indexing Γ Λ σ) (S : Nat)
    (cursor : Fin S) (symbol : Fin indexing.symbolCount) (j : Fin (indexing.width S))
    (hj : j.val = indexing.labelCount + indexing.stateCount +
      cursor.val * indexing.symbolCount + symbol.val) :
    (indexing.configIndexEquiv S).symm j =
      (let a := indexing.symbols.symm symbol
       Sum.inr (Sum.inr ⟨a.1, cursor, a.2⟩) : ConfigBit Γ Λ σ S) := by
  dsimp only
  apply (indexing.configIndexEquiv S).injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  rw [ConfigIndex.Indexing.configIndex_cell]
  simpa only [Sigma.eta, Equiv.apply_symm_apply] using hj

theorem outputOrder_eq_blocks (indexing : ConfigIndex.Indexing Γ Λ σ) (S : Nat) :
    TransitionTemplate.outputOrder indexing S =
      ((List.finRange indexing.labelCount).map fun i =>
        (Sum.inl (indexing.labels.symm i) : ConfigBit Γ Λ σ S)) ++
      ((List.finRange indexing.stateCount).map fun i =>
        (Sum.inr (Sum.inl (indexing.states.symm i)) : ConfigBit Γ Λ σ S)) ++
      ((List.finRange S).flatMap fun cursor =>
        (List.finRange indexing.symbolCount).map fun j =>
          let a := indexing.symbols.symm j
          (Sum.inr (Sum.inr ⟨a.1, cursor, a.2⟩) : ConfigBit Γ Λ σ S)) := by
  simp only [TransitionTemplate.outputOrder, List.flatMap_def, ← List.ofFn_eq_map]
  change List.ofFn (fun j : Fin (indexing.labelCount + indexing.stateCount +
      S * indexing.symbolCount) => (indexing.configIndexEquiv S).symm j) = _
  rw [List.ofFn_add (n := indexing.labelCount + indexing.stateCount)
    (m := S * indexing.symbolCount)]
  rw [List.ofFn_add (n := indexing.labelCount) (m := indexing.stateCount)]
  rw [List.ofFn_mul (m := S) (n := indexing.symbolCount)]
  congr 1
  · congr 1
    · apply congrArg List.ofFn
      funext i
      exact unindex_label indexing S i _ rfl
    · apply congrArg List.ofFn
      funext i
      exact unindex_state indexing S i _ rfl
  · apply congrArg List.flatten
    apply congrArg List.ofFn
    funext cursor
    apply congrArg List.ofFn
    funext symbol
    apply unindex_cell indexing S cursor symbol
    simp only [Fin.val_natAdd]
    omega

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.OutputOrder

end

end OAI
