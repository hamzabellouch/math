import OAI.Combinatorics.Ramsey.CycleClique.Construction.AssignedLabels

namespace OAI

/-! Operations on the assigned amounts of a chain. -/

namespace CycleClique.Construction.AssignedAmounts

open scoped Classical

variable {V : Type*} {Q : Finset V}

theorem append_segment {A J B : List V} {y : V} {w W : List ℕ}
    (hA : AssignedAmounts Q A w) (hAne : A ≠ [])
    (hJ : ∀ z ∈ J, z ∉ Q) (hJne : J ≠ [])
    (hB : AssignedAmounts Q (y :: B) W) :
    AssignedAmounts Q (A ++ J ++ y :: B) (w ++ J.length :: W) := by
  have hy : y ∈ Q := by
    cases hB with
    | singleton hy => exact hy
    | step hy => exact hy
  induction hA with
  | nil => exact False.elim (hAne rfl)
  | singleton hx => simpa using AssignedAmounts.step hx hy hJ hJne hB
  | @step x z K C u hx hz hK hKne ht ih =>
    have hh := ih (by simp)
    simpa [List.append_assoc] using AssignedAmounts.step hx hz hK hKne hh

theorem reverse {l : List V} {w : List ℕ} (h : AssignedAmounts Q l w) :
    AssignedAmounts Q l.reverse w.reverse := by
  induction h with
  | nil => exact .nil
  | singleton hx => simpa using AssignedAmounts.singleton hx
  | @step x y J B w hx hy hJ hne ht ih =>
    have hrevJ : ∀ z ∈ J.reverse, z ∉ Q := by simpa using hJ
    have hh := append_segment ih (by simp) hrevJ (by simpa using hne) (.singleton hx)
    simpa [List.reverse_cons, List.reverse_append, List.append_assoc] using hh

end CycleClique.Construction.AssignedAmounts

end OAI
