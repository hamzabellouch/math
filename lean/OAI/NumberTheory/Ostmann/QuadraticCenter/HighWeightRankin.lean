import OAI.NumberTheory.Ostmann.QuadraticCenter.RightJacobiMomentReindex

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem squarefree_weight_sum_le_euler_product (P S : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hS : ∀ n ∈ S, Squarefree n)
    (hcover : ∀ n ∈ S, n.primeFactors ⊆ P) {w : ℝ} (hw : 0 ≤ w) :
    (∑ n ∈ S, w ^ n.primeFactors.card / (n : ℝ)) ≤ ∏ p ∈ P, (1 + w / (p : ℝ)) := by
  classical
  have heq (s : Finset P) :
      w ^ (primeSubsetProduct s).primeFactors.card / (primeSubsetProduct s : ℝ) =
        ∏ p ∈ s, w / (p.val : ℝ) := by
    rw [primeSubsetProduct_primeFactors_card hP, Finset.prod_div_distrib]
    simp only [Finset.prod_const, primeSubsetProduct, Nat.cast_prod]
  calc
    _ = ∑ s : Finset P, if primeSubsetProduct s ∈ S then
        w ^ (primeSubsetProduct s).primeFactors.card / (primeSubsetProduct s : ℝ) else 0 :=
      (sum_primeSubsetProduct hP S hS hcover _).symm
    _ ≤ ∑ s : Finset P,
        w ^ (primeSubsetProduct s).primeFactors.card / (primeSubsetProduct s : ℝ) := by
      apply Finset.sum_le_sum
      intro s hs
      split_ifs
      · exact le_rfl
      · positivity
    _ = ∑ s : Finset P, ∏ p ∈ s, w / (p.val : ℝ) := Finset.sum_congr rfl (fun s hs => heq s)
    _ = ∏ p : P, (1 + w / (p.val : ℝ)) := by
      simpa only [Finset.powerset_univ] using
        (Finset.prod_one_add (f := fun p : P => w / (p.val : ℝ)) Finset.univ).symm
    _ = _ := Finset.prod_coe_sort P (fun p => 1 + w / (p : ℝ))

theorem squarefree_rankin_tail_le (P S : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hS : ∀ n ∈ S, Squarefree n)
    (hcover : ∀ n ∈ S, n.primeFactors ⊆ P) (k : ℕ)
    (hk : ∀ n ∈ S, k ≤ n.primeFactors.card) {w v : ℝ} (hw : 0 ≤ w) (hv : 1 ≤ v) :
    (∑ n ∈ S, w ^ n.primeFactors.card / (n : ℝ)) ≤
      (∏ p ∈ P, (1 + w * v / (p : ℝ))) / v ^ k := by
  have hv0 : 0 < v := lt_of_lt_of_le zero_lt_one hv
  apply (le_div_iff₀ (pow_pos hv0 k)).mpr
  calc
    (∑ n ∈ S, w ^ n.primeFactors.card / (n : ℝ)) * v ^ k =
        ∑ n ∈ S, (w ^ n.primeFactors.card / (n : ℝ)) * v ^ k := by rw [Finset.sum_mul]
    _ ≤ ∑ n ∈ S, (w * v) ^ n.primeFactors.card / (n : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      calc
        _ ≤ (w ^ n.primeFactors.card / (n : ℝ)) * v ^ n.primeFactors.card :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hv (hk n hn)) (by positivity)
        _ = _ := by rw [mul_pow]; ring
    _ ≤ _ := squarefree_weight_sum_le_euler_product P S hP hS hcover (mul_nonneg hw hv0.le)

theorem squarefree_rankin_tail_le_exp (P S : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hS : ∀ n ∈ S, Squarefree n)
    (hcover : ∀ n ∈ S, n.primeFactors ⊆ P) (k : ℕ)
    (hk : ∀ n ∈ S, k ≤ n.primeFactors.card) {w v : ℝ} (hw : 0 ≤ w) (hv : 1 ≤ v) :
    (∑ n ∈ S, w ^ n.primeFactors.card / (n : ℝ)) ≤
      Real.exp (w * v * ∑ p ∈ P, 1 / (p : ℝ)) / v ^ k := by
  apply (squarefree_rankin_tail_le P S hP hS hcover k hk hw hv).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hp := Real.prod_one_add_le_exp_sum P
    (f := fun p : ℕ => w * v / (p : ℝ)) (fun p => by positivity)
  have heq : (∑ p ∈ P, w * v / (p : ℝ)) = w * v * ∑ p ∈ P, 1 / (p : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  simpa only [heq] using hp

end Ostmann.QuadraticCenter

end OAI
