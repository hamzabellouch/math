import OAI.Combinatorics.Ramsey.CycleClique.Construction.PathSystem

namespace OAI

/-! Elementary list surgery used to insert an outside detour in a chain. -/

namespace CycleClique.Construction
theorem chain_outside_interior {V : Type*} {Q : Finset V} {x y : V} {J : List V}
    (hxy : ¬ (x ∈ Q ∧ y ∈ Q)) (hJ : ∀ z ∈ J, z ∉ Q) :
    (x :: (J ++ [y])).IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)) := by
  induction J generalizing x with
  | nil => simpa using hxy
  | cons z J ih =>
    simp only [List.cons_append, List.isChain_cons_cons]
    refine ⟨fun h => hJ z (by simp) h.2, ?_⟩
    exact ih (fun h => hJ z (by simp) h.1) (fun w hw => hJ w (by simp [hw]))

theorem chain_outside_interior_of_ne_nil {V : Type*} {Q : Finset V}
    {x y : V} {J : List V} (hne : J ≠ []) (hJ : ∀ z ∈ J, z ∉ Q) :
    (x :: (J ++ [y])).IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)) := by
  cases J with
  | nil => exact False.elim (hne rfl)
  | cons z J =>
    simp only [List.cons_append, List.isChain_cons_cons]
    refine ⟨fun h => hJ z (by simp) h.2, ?_⟩
    exact chain_outside_interior (fun h => hJ z (by simp) h.1)
      (fun w hw => hJ w (by simp [hw]))

theorem reverse_join_chain {V : Type*} {R : V → V → Prop}
    (hsym : ∀ ⦃a b⦄, R a b → R b a) {B D J : List V} {x y : V}
    (hleft : (x :: B).IsChain R) (hright : (y :: D).IsChain R)
    (hjoin : (x :: (J ++ [y])).IsChain R) :
    (B.reverse ++ x :: (J ++ y :: D)).IsChain R := by
  apply List.isChain_split.mpr
  constructor
  · have hr : (x :: B).reverse.IsChain R := List.isChain_reverse.mpr (hleft.imp hsym)
    simpa using hr
  · exact List.isChain_cons_split.mpr ⟨hjoin, hright⟩

theorem nodup_insert_list {V : Type*} {A B J : List V}
    (hold : (A ++ B).Nodup) (hJ : J.Nodup) (hdis : J.Disjoint (A ++ B)) :
    (A ++ J ++ B).Nodup := by
  have h := hold.append hJ hdis.symm
  have hp := (show (J ++ B).Perm (B ++ J) from List.perm_append_comm).append_left A
  have hn := hp.nodup_iff.mpr (show (A ++ (B ++ J)).Nodup by
    simpa only [List.append_assoc] using h)
  simpa only [List.append_assoc] using hn

theorem chain_insert_between {V : Type*} {R : V → V → Prop} {A B J : List V} {x y : V}
    (hold : (A ++ x :: y :: B).IsChain R)
    (hnew : (x :: (J ++ [y])).IsChain R) :
    (A ++ x :: (J ++ y :: B)).IsChain R := by
  have ho := List.isChain_append_cons_cons.mp hold
  apply List.isChain_split.mpr
  refine ⟨ho.1, ?_⟩
  exact List.isChain_cons_split.mpr ⟨hnew, ho.2.2⟩

theorem head_insert_between {V : Type*} (A B J : List V) (x y : V) :
    (A ++ x :: (J ++ y :: B)).head? = (A ++ x :: y :: B).head? := by
  simp

theorem last_insert_between {V : Type*} (A B J : List V) (x y : V) :
    (A ++ x :: (J ++ y :: B)).getLast? = (A ++ x :: y :: B).getLast? := by
  have htail : (y :: B).getLast? = some ((y :: B).getLast (by simp)) :=
    List.getLast?_eq_some_getLast (by simp)
  have hold : A ++ x :: y :: B = (A ++ [x]) ++ (y :: B) := by
    simp only [List.append_assoc, List.singleton_append]
  have hnew : A ++ x :: (J ++ y :: B) = (A ++ [x] ++ J) ++ (y :: B) := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [hold, hnew]
  simp only [List.getLast?_append, htail, Option.or]

end CycleClique.Construction

end OAI
