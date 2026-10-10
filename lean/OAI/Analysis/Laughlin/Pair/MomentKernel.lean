import OAI.Analysis.Laughlin.Pair.Moment

namespace OAI

namespace Laughlin
open scoped BigOperators

theorem pairMoment_zero_outside (Q p : ℕ) (hp : 2*Q-2 < p)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ) : pairMoment Q p ψ = 0 := by
  unfold pairMoment
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  by_cases hs : x.val+y.val = p+1
  · rw [ite_eq_left hs]
    have hxy : x.val = y.val := by omega
    simp [hxy]
  · simp [hs]

theorem pairMoment_zero_of_pair_kernel (Q : ℕ) (hQ : 2 ≤ Q)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ)
    (hk : ∀ p ∈ Finset.range (2*Q-1),
      (∑ x, ∑ y, (pairCoefficient Q p x y : ℂ)*ψ x y) = 0) (p : ℕ) :
    pairMoment Q p ψ = 0 := by
  by_cases hp : p ≤ 2*Q-2
  · rw [pairMoment_eq_amplitude Q p (by omega) hp ψ, hk p (by simpa using (show p < 2*Q-1 by omega)), mul_zero]
  · exact pairMoment_zero_outside Q p (by omega) ψ

theorem pair_jet_coefficient_zero (Q n : ℕ) (ψ : Fin (Q+1) → Fin (Q+1) → ℂ)
    (ha : ∀ x y, ψ y x = -ψ x y) (hm : pairMoment Q n ψ = 0) :
    (∑ x, ∑ y, if x.val+y.val = n+1 then
      (y.val : ℂ)*weightedPairCoordinate Q ψ x y else 0) = 0 := by
  let I : ℂ := ∑ x, ∑ y, if x.val+y.val = n+1 then
    (x.val : ℂ)*weightedPairCoordinate Q ψ x y else 0
  let J : ℂ := ∑ x, ∑ y, if x.val+y.val = n+1 then
    (y.val : ℂ)*weightedPairCoordinate Q ψ x y else 0
  have hs : I = -J := by
    dsimp [I,J]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    rw [weightedPairCoordinate_swap Q ψ ha x y, Nat.add_comm y.val x.val]
    split_ifs <;> ring
  have hmom : pairMoment Q n ψ = I-J := by
    dsimp [pairMoment,I,J]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    split_ifs <;> ring
  have hz : (2 : ℂ)*J = 0 := by
    calc
      _ = -(I-J) := by rw [hs]; ring
      _ = 0 := by rw [← hmom, hm]; simp
  exact (mul_eq_zero.mp hz).resolve_left two_ne_zero

end Laughlin

end OAI
