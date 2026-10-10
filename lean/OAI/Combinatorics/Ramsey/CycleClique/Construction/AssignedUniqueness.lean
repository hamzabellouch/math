import OAI.Combinatorics.Ramsey.CycleClique.Construction.AssignedSubcollection

namespace OAI

/-! Assigned amounts are uniquely determined by a chain and its clique. -/

namespace CycleClique.Construction
variable {V : Type*} {Q : Finset V}

private theorem outside_prefix_unique {J K B C : List V} {y z : V}
    (hJ : ∀ v ∈ J, v ∉ Q) (hK : ∀ v ∈ K, v ∉ Q) (hy : y ∈ Q) (hz : z ∈ Q)
    (heq : J ++ y :: B = K ++ z :: C) : J = K ∧ y = z ∧ B = C := by
  induction J generalizing K with
  | nil =>
    cases K with
    | nil => exact ⟨rfl, (List.cons.inj heq).1, (List.cons.inj heq).2⟩
    | cons k K =>
      have hyk : y = k := (List.cons.inj heq).1
      exact False.elim (hK k (by simp) (by simpa only [← hyk] using hy))
  | cons j J ih =>
    cases K with
    | nil =>
      have hjz : j = z := (List.cons.inj heq).1
      exact False.elim (hJ j (by simp) (by simpa only [hjz] using hz))
    | cons k K =>
      have hh : j = k ∧ J ++ y :: B = K ++ z :: C := List.cons.inj heq
      obtain ⟨hJK, hyz, hBC⟩ := ih (fun v hv => hJ v (by simp [hv]))
        (fun v hv => hK v (by simp [hv])) hh.2
      exact ⟨by simp [hh.1, hJK], hyz, hBC⟩

namespace AssignedAmounts

theorem equal_of_chain_eq {l l' : List V} {w w' : List ℕ}
    (h : AssignedAmounts Q l w) (h' : AssignedAmounts Q l' w') (heq : l = l') : w = w' := by
  induction h generalizing l' w' with
  | nil =>
    cases h' with
    | nil => rfl
    | singleton => simp at heq
    | step => simp at heq
  | singleton hx =>
    cases h' with
    | nil => simp at heq
    | singleton => rfl
    | @step x y J B w hx hy hJ hne ht =>
      have hh := congrArg List.length heq
      simp only [List.length_cons, List.length_append, List.length_nil] at hh
      omega
  | @step x y J B w hx hy hJ hne ht ih =>
    cases h' with
    | nil => simp at heq
    | singleton =>
      have hh := congrArg List.length heq
      simp only [List.length_cons, List.length_append, List.length_nil] at hh
      omega
    | @step x' y' K C W hx' hy' hK hKne ht' =>
      have hh : x = x' ∧ J ++ y :: B = K ++ y' :: C := List.cons.inj heq
      obtain ⟨hJK, hyy, hBC⟩ := outside_prefix_unique hJ hK hy hy' hh.2
      subst K
      subst y'
      subst C
      have hw := ih ht' rfl
      simp only [hw]

theorem unique {l : List V} {w w' : List ℕ}
    (h : AssignedAmounts Q l w) (h' : AssignedAmounts Q l w') : w = w' :=
  h.equal_of_chain_eq h' rfl

end AssignedAmounts

namespace SystemAssignedAmounts

theorem equal_of_chains_eq {C D : List (List V)} {w W : List ℕ}
    (h : SystemAssignedAmounts Q C w) (h' : SystemAssignedAmounts Q D W)
    (heq : C = D) : w = W := by
  induction h generalizing D W with
  | nil =>
    cases h' with
    | nil => rfl
    | cons => simp at heq
  | @cons l C w W hh ht ih =>
    cases h' with
    | nil => simp at heq
    | @cons l' D w' W' hh' ht' =>
      have hc := List.cons.inj heq
      rw [hh.equal_of_chain_eq hh' hc.1, ih ht' hc.2]

theorem unique {C : List (List V)} {w W : List ℕ}
    (h : SystemAssignedAmounts Q C w) (h' : SystemAssignedAmounts Q C W) : w = W :=
  h.equal_of_chains_eq h' rfl

end SystemAssignedAmounts

end CycleClique.Construction

end OAI
