import OAI.Combinatorics.Ramsey.CycleClique.Construction.AssignedAmounts

namespace OAI

/-! Locate an arbitrary assigned segment together with the amount decompositions of its two sides. -/

namespace CycleClique.Construction.AssignedAmounts

open scoped Classical

variable {V : Type*} {Q : Finset V}

theorem cut {l : List V} {w : List ℕ} (h : AssignedAmounts Q l w)
    {A B : List ℕ} {a : ℕ} (heq : w = A ++ a :: B) :
    ∃ P J R x y, l = P ++ x :: (J ++ y :: R) ∧ x ∈ Q ∧ y ∈ Q ∧
      (∀ z ∈ J, z ∉ Q) ∧ J.length = a ∧
      AssignedAmounts Q (P ++ [x]) A ∧ AssignedAmounts Q (y :: R) B := by
  induction h generalizing A B a with
  | nil => cases A <;> simp at heq
  | singleton hx => cases A <;> simp at heq
  | @step x y J R w hx hy hJ hne ht ih =>
    cases A with
    | nil =>
      have hh : J.length = a ∧ w = B := List.cons.inj heq
      obtain ⟨rfl, rfl⟩ := hh
      exact ⟨[], J, R, x, y, rfl, hx, hy, hJ, rfl, .singleton hx, ht⟩
    | cons b A =>
      have hh : J.length = b ∧ w = A ++ a :: B := List.cons.inj heq
      obtain ⟨P', J', R', x', y', heq', hx', hy', hJ', hlen', hpre, hsuf⟩ := ih hh.2
      have hpreNew : AssignedAmounts Q ((x :: (J ++ P')) ++ [x']) (J.length :: A) := by
        cases P' with
        | nil =>
          have hyx : y = x' := (List.cons.inj heq').1
          subst x'
          simpa only [List.append_nil, List.cons_append, List.nil_append] using
            (AssignedAmounts.step hx hy hJ hne hpre)
        | cons z P' =>
          have hyz : y = z := (List.cons.inj heq').1
          subst z
          simpa [List.append_assoc] using
            (AssignedAmounts.step hx hy hJ hne hpre)
      refine ⟨x :: (J ++ P'), J', R', x', y', ?_, hx', hy', hJ', hlen', ?_, hsuf⟩
      · rw [heq']
        simp only [List.cons_append, List.append_assoc]
      · simpa only [hh.1] using hpreNew

end CycleClique.Construction.AssignedAmounts

end OAI
