import OAI.Combinatorics.ContingencyTables.Transport.IntegerSliceRestriction

namespace OAI

/-! # A fixed context after a physical coordinate bijection -/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical
open BalancedBox

variable {C D S : Type*} [Fintype C] [Fintype D] [Fintype S]
  [DecidableEq C] [DecidableEq D] [DecidableEq S]

theorem context_slices (e : (C ⊕ D) ≃ S) (f : (S → ℕ) → ℝ)
    (mC c : C → ℕ) (mD : D → ℕ) (R : ℕ) (hc : InBox mC c)
    (hp : PositiveSlice f ((Sum.elim mC mD) ∘ e.symm) ((∑ i, c i)+R))
    (hs : RemovalSlice f ((Sum.elim mC mD) ∘ e.symm) ((∑ i, c i)+R)) :
    PositiveSlice (fun x => f ((Sum.elim c x) ∘ e.symm)) mD R ∧
      RemovalSlice (fun x => f ((Sum.elim c x) ∘ e.symm)) mD R := by
  have hpr := positiveSlice_reindex e f _ _ hp
  have hsr := removalSlice_reindex e f _ _ hs
  have hm : ((Sum.elim mC mD) ∘ e.symm) ∘ e=Sum.elim mC mD := by
    funext t
    simp only [Function.comp_apply,Equiv.symm_apply_apply]
  rw [hm] at hpr hsr
  exact ⟨positiveSlice_fixed (fun x => f (x ∘ e.symm)) mC c mD R hc hpr,
    removalSlice_fixed (fun x => f (x ∘ e.symm)) mC c mD R hc hsr⟩

end ContingencyTables.IntegerWeightedTransport

end OAI
