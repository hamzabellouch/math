import OAI.Combinatorics.Ramsey.CycleClique.Construction.AssignedDeletion

namespace OAI

/-! Recover the individual positive amounts of a chain by cutting exactly
at its clique vertices. This decomposition is used for subcollections and
for the finite path-pattern domain. -/

namespace CycleClique.Construction
open scoped Classical

variable {V : Type*} {Q : Finset V}

inductive AssignedAmounts (Q : Finset V) : List V → List ℕ → Prop
  | nil : AssignedAmounts Q [] []
  | singleton {x : V} (hx : x ∈ Q) : AssignedAmounts Q [x] []
  | step {x y : V} {J B : List V} {w : List ℕ}
      (hx : x ∈ Q) (hy : y ∈ Q) (hJ : ∀ z ∈ J, z ∉ Q) (hne : J ≠ [])
      (tail : AssignedAmounts Q (y :: B) w) :
      AssignedAmounts Q (x :: (J ++ y :: B)) (J.length :: w)

theorem exists_first_clique {l : List V} (h : ∃ y ∈ l, y ∈ Q) :
    ∃ J y B, l = J ++ y :: B ∧ (∀ z ∈ J, z ∉ Q) ∧ y ∈ Q := by
  classical
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    by_cases hx : x ∈ Q
    · exact ⟨[], x, xs, rfl, by simp, hx⟩
    · have ht : ∃ y ∈ xs, y ∈ Q := by
        obtain ⟨y, hy, hyQ⟩ := h
        rcases List.mem_cons.mp hy with rfl | hy
        · exact False.elim (hx hyQ)
        · exact ⟨y, hy, hyQ⟩
      obtain ⟨J, y, B, heq, hJ, hy⟩ := ih ht
      refine ⟨x :: J, y, B, by simp only [List.cons_append, heq], ?_, hy⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hx
      · exact hJ z hz

theorem exists_assignedAmounts {l : List V}
    (hends : (∀ v ∈ l.head?, v ∈ Q) ∧ (∀ v ∈ l.getLast?, v ∈ Q))
    (hsteps : l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q))) :
    ∃ w, AssignedAmounts Q l w := by
  classical
  suffices hh : ∀ n, ∀ l : List V, l.length = n →
      ((∀ v ∈ l.head?, v ∈ Q) ∧ (∀ v ∈ l.getLast?, v ∈ Q)) →
      l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q)) →
      ∃ w, AssignedAmounts Q l w by
    exact hh l.length l rfl hends hsteps
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro l hlen hends hsteps
    cases l with
    | nil => exact ⟨[], .nil⟩
    | cons x xs =>
      have hx : x ∈ Q := hends.1 x (by simp)
      by_cases hxs : xs = []
      · subst xs
        exact ⟨[], .singleton hx⟩
      · have hlast : xs.getLast hxs ∈ Q := by
          apply hends.2
          rw [List.getLast?_cons_of_ne_nil hxs]
          exact List.getLast?_eq_some_getLast hxs
        obtain ⟨J, y, B, heq, hJ, hy⟩ :=
          exists_first_clique ⟨xs.getLast hxs, List.getLast_mem hxs, hlast⟩
        have hJne : J ≠ [] := by
          intro he
          subst J
          simp only [List.nil_append] at heq
          subst xs
          exact (List.isChain_cons_cons.mp hsteps).1 ⟨hx, hy⟩
        have hsmall : (y :: B).length < n := by
          simp only [List.length_cons, heq, List.length_append] at hlen
          simp only [List.length_cons]
          omega
        have htends : (∀ v ∈ (y :: B).head?, v ∈ Q) ∧
            (∀ v ∈ (y :: B).getLast?, v ∈ Q) := by
          refine ⟨by simpa using hy, ?_⟩
          intro v hv
          apply hends.2 v
          rw [List.getLast?_cons_of_ne_nil hxs, heq, List.getLast?_append,
            List.getLast?_eq_some_getLast (show y :: B ≠ [] by simp)]
          simpa only [List.getLast?_eq_some_getLast (show y :: B ≠ [] by simp), Option.or]
            using hv
        have htsteps : (y :: B).IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)) := by
          have hh := (List.isChain_cons.mp hsteps).2
          rw [heq] at hh
          exact (List.isChain_append.mp hh).2.1
        obtain ⟨w, hw⟩ := ih _ hsmall (y :: B) rfl htends htsteps
        refine ⟨J.length :: w, ?_⟩
        rw [heq]
        exact .step hx hy hJ hJne hw

namespace AssignedAmounts

theorem positive {l : List V} {w : List ℕ} (h : AssignedAmounts Q l w) :
    ∀ a ∈ w, 0 < a := by
  induction h with
  | nil => simp
  | singleton => simp
  | @step x y J B w hx hy hJ hne ht ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact List.length_pos_iff.mpr hne
    · exact ih a ha

theorem sum_eq {l : List V} {w : List ℕ} (h : AssignedAmounts Q l w) :
    w.sum = chainOutsideCount Q l := by
  induction h with
  | nil => rfl
  | singleton hx => simp [chainOutsideCount, hx]
  | @step x y J B w hx hy hJ hne ht ih =>
    have hfilter : J.filter (fun z => decide (z ∉ Q)) = J := by
      apply List.filter_eq_self.mpr
      intro z hz
      simpa using hJ z hz
    simp only [List.sum_cons, chainOutsideCount, List.filter_cons, hx,
      not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
      List.filter_append, List.length_append, hfilter] at ih ⊢
    rw [ih]

theorem length_eq {l : List V} {w : List ℕ} (h : AssignedAmounts Q l w) :
    w.length = chainCliqueCount Q l - 1 := by
  induction h with
  | nil => rfl
  | singleton hx => simp [chainCliqueCount, hx]
  | @step x y J B w hx hy hJ hne ht ih =>
    have hzero := chainCliqueCount_eq_zero hJ
    have hxcount : chainCliqueCount Q [x] = 1 := by simp [chainCliqueCount, hx]
    have hypos : 1 ≤ chainCliqueCount Q (y :: B) :=
      chainCliqueCount_pos (by simp) (by simpa using hy)
    change (_ :: _).length = chainCliqueCount Q ([x] ++ (J ++ y :: B)) - 1
    rw [chainCliqueCount_append, chainCliqueCount_append, hxcount, hzero]
    simp only [List.length_cons]
    omega

end AssignedAmounts

end CycleClique.Construction

end OAI
