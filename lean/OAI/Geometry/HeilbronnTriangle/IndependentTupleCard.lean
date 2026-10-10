import Mathlib

namespace OAI


open scoped BigOperators

namespace Problem355.IndependentTupleCard

variable (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]

theorem affineIndependent_fin_iff {n : ℕ} (p : Fin (n+1) → V) :
    AffineIndependent K p ↔
      LinearIndependent K (fun i : Fin n => p i.succ - p 0) := by
  rw [affineIndependent_iff_linearIndependent_vsub K p 0]
  simpa [Function.comp_def, finSuccAboveEquiv_apply, Fin.succAbove_zero] using
    (linearIndependent_equiv (finSuccAboveEquiv (0 : Fin (n+1)))
      (f := fun i : {x : Fin (n+1) // x ≠ 0} => p i -ᵥ p 0)).symm

def affineTupleEquiv (n : ℕ) :
    {p : Fin (n+1) → V // AffineIndependent K p} ≃
      V × {v : Fin n → V // LinearIndependent K v} where
  toFun p := (p.val 0, ⟨fun i => p.val i.succ - p.val 0,
    (affineIndependent_fin_iff K V p.val).mp p.property⟩)
  invFun xv := ⟨Fin.cons xv.1 (fun i => xv.2.val i + xv.1), by
    apply (affineIndependent_fin_iff K V _).mpr
    simpa using xv.2.property⟩
  left_inv p := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  right_inv xv := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      funext i
      simp

variable [Fintype K] [Finite V]

theorem card_affineIndependent {n : ℕ} (hn : n ≤ Module.finrank K V) :
    Nat.card {p : Fin (n+1) → V // AffineIndependent K p} =
      Nat.card V * ∏ i : Fin n,
        (Fintype.card K ^ Module.finrank K V - Fintype.card K ^ i.val) := by
  rw [Nat.card_congr (affineTupleEquiv K V n), Nat.card_prod, card_linearIndependent hn]

theorem card_independent_pairs :
    Nat.card {p : Fin 2 → (Fin 3 → K) // LinearIndependent K p} =
      (Fintype.card K ^ 3 - 1) * (Fintype.card K ^ 3 - Fintype.card K) := by
  have hn : 2 ≤ Module.finrank K (Fin 3 → K) := by simp
  rw [card_linearIndependent hn]
  simp [Fin.prod_univ_two]

theorem card_affineIndependent_triples :
    Nat.card {p : Fin 3 → (Fin 3 → K) // AffineIndependent K p} =
      Fintype.card K ^ 3 * (Fintype.card K ^ 3 - 1) *
        (Fintype.card K ^ 3 - Fintype.card K) := by
  have hn : 2 ≤ Module.finrank K (Fin 3 → K) := by simp
  rw [card_affineIndependent K (Fin 3 → K) hn]
  simp [Nat.card_eq_fintype_card, Fin.prod_univ_two, mul_assoc]

end Problem355.IndependentTupleCard

end OAI
