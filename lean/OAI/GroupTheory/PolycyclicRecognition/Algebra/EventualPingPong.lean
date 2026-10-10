import OAI.GroupTheory.PolycyclicRecognition.Algebra.CyclicPingPong

namespace OAI

/-! # Large powers of contracting transformations generate a free group

Uniform control of sufficiently large positive and negative powers on the
other attracting domain suffices. A common power turns these estimates into
the cyclic ping-pong criterion.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Pointwise Function

variable {G X : Type} [Group G] [MulAction G X]

theorem eventual_ping_pong_free_power (a : Bool → G) (D : Bool → Set X)
    (hne : ∀ i, (D i).Nonempty) (hdis : Pairwise (Disjoint on D))
    (hevent : ∀ i, ∃ N : ℕ, ∀ j, i ≠ j → ∀ n ≥ N,
      ((a i) ^ n • D j ⊆ D i) ∧ ((a i)⁻¹ ^ n • D j ⊆ D i)) :
    ∃ N : ℕ, 0 < N ∧ Function.Injective (FreeGroup.lift (fun i => (a i) ^ N)) := by
  choose N hN using hevent
  let M := max (N false) (N true) + 1
  have hMpos : 0 < M := Nat.succ_pos _
  have hNM (i : Bool) : N i ≤ M := by
    cases i
    · exact (le_max_left _ _).trans (Nat.le_succ _)
    · exact (le_max_right _ _).trans (Nat.le_succ _)
  refine ⟨M, hMpos, cyclic_ping_pong_injective _ D hne hdis ?_⟩
  intro i j hij m hm
  cases m with
  | ofNat k =>
    have hk : 0 < k := by
      by_contra hh
      have hz : k = 0 := Nat.eq_zero_of_not_pos hh
      exact hm (by simp [hz])
    rw [Int.ofNat_eq_natCast, zpow_natCast, ← pow_mul]
    exact (hN i j hij (M * k) ((hNM i).trans (Nat.le_mul_of_pos_right M hk))).1
  | negSucc k =>
    rw [zpow_negSucc, ← pow_mul, ← inv_pow]
    exact (hN i j hij (M * (k + 1))
      ((hNM i).trans (Nat.le_mul_of_pos_right M (Nat.succ_pos k)))).2

end PolycyclicRecognition

end

end OAI
