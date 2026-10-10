import Mathlib.Data.Fin.Tuple.Basic

namespace OAI

namespace Yau

theorem exists_sequence_of_finite_history {X : ℕ → Type*} (x₀ : X 0)
    (R : (n : ℕ) → ((i : Fin (n+1)) → X i.val) → X (n+1) → Prop)
    (H : ∀ n v, ∃ w, R n v w) :
    ∃ x : (n : ℕ) → X n, x 0=x₀ ∧ ∀ n, R n (fun i ↦ x i.val) (x (n+1)) := by
  classical
  choose next hnext using H
  let rows : (n : ℕ) → (i : Fin (n+1)) → X i.val :=
    Nat.rec (Fin.snoc (fun i : Fin 0 ↦ Fin.elim0 i) x₀)
      (fun n v ↦ Fin.snoc v (next n v))
  let x : (n : ℕ) → X n := fun n ↦ rows n (Fin.last n)
  have hprefix : ∀ n (i : Fin (n+1)), rows n i=x i.val := by
    intro n
    induction n with
    | zero => intro i; have hi : i=Fin.last 0 := Fin.ext (by omega); subst i; rfl
    | succ n ih =>
      intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · rfl
      · change (Fin.snoc (α := fun i : Fin (n+2) ↦ X i.val) (rows n) (next n (rows n))) j.castSucc=x j.val
        rw [Fin.snoc_castSucc]
        exact ih j
  refine ⟨x,?_,?_⟩
  · change Fin.snoc (α := fun i : Fin 1 ↦ X i.val) (fun i : Fin 0 ↦ Fin.elim0 i) x₀ (Fin.last 0)=x₀
    rw [Fin.snoc_last]
  · intro n
    have hp : rows n=(fun i : Fin (n+1) ↦ x i.val) := funext (hprefix n)
    have he : x (n+1)=next n (rows n) := by
      change Fin.snoc (α := fun i : Fin (n+2) ↦ X i.val) (rows n) (next n (rows n)) (Fin.last (n+1))=next n (rows n)
      rw [Fin.snoc_last]
    rw [he,← hp]
    exact hnext n (rows n)

end Yau

end OAI
