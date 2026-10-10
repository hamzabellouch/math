import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import OAI.NumberTheory.Ostmann.Tree.PartitionMatching

namespace OAI

/-! # The bipartite overlap graph of an actual bulk permutation -/

namespace Ostmann

open scoped Classical

def arrangementGraph {L : Type*} (m : ℕ) (e : Equiv.Perm (L × Fin m)) :
    SimpleGraph (L ⊕ L) where
  Adj x y := match x, y with
    | .inl a, .inr b => ∃ i j, e (a, i) = (b, j)
    | .inr b, .inl a => ∃ i j, e (a, i) = (b, j)
    | _, _ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> exact id⟩
  loopless := ⟨by intro x; cases x <;> exact not_false⟩

noncomputable instance {L : Type*} [Fintype L] (m : ℕ)
    (e : Equiv.Perm (L × Fin m)) : Fintype (arrangementGraph m e).ConnectedComponent :=
  Fintype.ofFinite _

def arrangementLeft {L : Type*} {m : ℕ} (e : Equiv.Perm (L × Fin m))
    (l : L) : (arrangementGraph m e).ConnectedComponent :=
  (arrangementGraph m e).connectedComponentMk (.inl l)

def arrangementRight {L : Type*} {m : ℕ} (e : Equiv.Perm (L × Fin m))
    (l : L) : (arrangementGraph m e).ConnectedComponent :=
  (arrangementGraph m e).connectedComponentMk (.inr l)

theorem arrangement_components_match {L : Type*} {m : ℕ}
    (e : Equiv.Perm (L × Fin m)) (x : L × Fin m) :
    arrangementRight e (e x).1 = arrangementLeft e x.1 := by
  apply Eq.symm
  apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
  exact ⟨x.2, (e x).2, rfl⟩

def arrangementMatching {L : Type*} {m : ℕ}
    (e : Equiv.Perm (L × Fin m)) :
    PartitionMatching (fun x : L × Fin m => arrangementLeft e x.1)
      (fun x : L × Fin m => arrangementRight e x.1) :=
  ⟨e, arrangement_components_match e⟩

theorem arrangementLeft_surjective {L : Type*} {m : ℕ} (hm : 0 < m)
    (e : Equiv.Perm (L × Fin m)) : Function.Surjective (arrangementLeft e) := by
  intro c
  induction c using SimpleGraph.ConnectedComponent.ind with
  | h v =>
    cases v with
    | inl l => exact ⟨l, rfl⟩
    | inr l =>
      let x := e.symm (l, ⟨0, hm⟩)
      refine ⟨x.1, ?_⟩
      have h := arrangement_components_match e x
      simpa only [x, Equiv.apply_symm_apply, arrangementRight] using h.symm

theorem arrangementRight_surjective {L : Type*} {m : ℕ} (hm : 0 < m)
    (e : Equiv.Perm (L × Fin m)) : Function.Surjective (arrangementRight e) := by
  intro c
  obtain ⟨l, rfl⟩ := arrangementLeft_surjective hm e c
  exact ⟨(e (l, ⟨0, hm⟩)).1, arrangement_components_match e (l, ⟨0, hm⟩)⟩

/-- Counting the slots in a component from the two sides gives equal
leaf counts, because every leaf has exactly m slots. -/
theorem arrangement_component_balance {L : Type*} [Fintype L] {m : ℕ}
    (hm : 0 < m) (e : Equiv.Perm (L × Fin m))
    (c : (arrangementGraph m e).ConnectedComponent) :
    Fintype.card {l : L // arrangementLeft e l = c} =
      Fintype.card {l : L // arrangementRight e l = c} := by
  have h := Fintype.card_congr ((arrangementMatching e).restrict c)
  simp only [card_slotFiber] at h
  exact Nat.eq_of_mul_eq_mul_right hm h

theorem arrangement_component_count_le {L : Type*} [Fintype L] {m : ℕ}
    (hm : 0 < m) (e : Equiv.Perm (L × Fin m)) :
    Fintype.card (arrangementGraph m e).ConnectedComponent ≤ Fintype.card L :=
  Fintype.card_le_of_surjective _ (arrangementLeft_surjective hm e)

end Ostmann

end OAI
