import OAI.Analysis.Laughlin.Pair.AffinePolynomial

namespace OAI

namespace Laughlin
open Polynomial
open scoped BigOperators

theorem pairMoment_eq_jet (Q n : ℕ) (ψ : Fin (Q+1) → Fin (Q+1) → ℂ)
    (ha : ∀ x y, ψ y x = -ψ x y) :
    pairMoment Q n ψ = -2 * ((pairAffinePolynomial Q ψ).derivative.eval
      (X : Polynomial ℂ)).coeff n := by
  rw [pairAffinePolynomial_jet_coeff]
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
  change pairMoment Q n ψ = -2*J
  rw [hmom,hs]
  ring

theorem pair_kernel_of_affine_cube (Q : ℕ) (hQ : 2 ≤ Q)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ) (ha : ∀ x y, ψ y x = -ψ x y)
    (hcube : PairDiagonal.diagonal^3 ∣ pairAffinePolynomial Q ψ) :
    ∀ p ∈ Finset.range (2*Q-1),
      (∑ x, ∑ y, (pairCoefficient Q p x y : ℂ)*ψ x y) = 0 := by
  obtain ⟨g,hg⟩ := hcube
  have hj : (pairAffinePolynomial Q ψ).derivative.eval (X : Polynomial ℂ) = 0 := by
    rw [hg, derivative_mul]
    simp [PairDiagonal.diagonal, derivative_pow]
  intro p hp
  have hp' : p ≤ 2*Q-2 := by have h := Finset.mem_range.mp hp; omega
  have hm : pairMoment Q p ψ = 0 := by
    rw [pairMoment_eq_jet Q p ψ ha, hj, coeff_zero]
    ring
  rw [pairMoment_eq_amplitude Q p (by omega) hp' ψ] at hm
  have hn : (pairNormalization Q p : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (pairNormalization_pos Q p (by omega) hp'))
  exact (mul_eq_zero.mp hm).resolve_left hn

theorem pair_kernel_iff_affine_cube (Q : ℕ) (hQ : 2 ≤ Q)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ) (ha : ∀ x y, ψ y x = -ψ x y) :
    (∀ p ∈ Finset.range (2*Q-1),
      (∑ x, ∑ y, (pairCoefficient Q p x y : ℂ)*ψ x y) = 0) ↔
        PairDiagonal.diagonal^3 ∣ pairAffinePolynomial Q ψ :=
  ⟨pair_kernel_affine_cube Q hQ ψ ha, pair_kernel_of_affine_cube Q hQ ψ ha⟩

end Laughlin

end OAI
