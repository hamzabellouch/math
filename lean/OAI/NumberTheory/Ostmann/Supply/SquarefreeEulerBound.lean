import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Ring.Finset
import OAI.NumberTheory.Ostmann.Characters.SquarefreeBonami

namespace OAI

/-! # The weighted reciprocal squarefree sum in the coefficient estimate -/

namespace Ostmann

open scoped BigOperators

theorem squarefree_weighted_reciprocal_le_product (S P : Finset ℕ)
    (hS : ∀ s ∈ S, Squarefree s) (hP : ∀ s ∈ S, s.primeFactors ⊆ P)
    (u : ℝ) (hu : 0 ≤ u) :
    (∑ s ∈ S, u ^ s.primeFactors.card / (s : ℝ)) ≤
      ∏ p ∈ P, (1 + u / (p : ℝ)) := by
  classical
  have hinj : Set.InjOn Nat.primeFactors (↑S : Set ℕ) := by
    intro a ha b hb he
    calc
      a = ∏ p ∈ a.primeFactors, p := (Nat.prod_primeFactors_of_squarefree (hS a ha)).symm
      _ = ∏ p ∈ b.primeFactors, p := by rw [he]
      _ = b := Nat.prod_primeFactors_of_squarefree (hS b hb)
  have hterm (s : ℕ) (hs : s ∈ S) :
      u ^ s.primeFactors.card / (s : ℝ) = ∏ p ∈ s.primeFactors, u / (p : ℝ) := by
    rw [Finset.prod_div_distrib, Finset.prod_const, ← Nat.cast_prod,
      Nat.prod_primeFactors_of_squarefree (hS s hs)]
  calc
    _ = ∑ s ∈ S, ∏ p ∈ s.primeFactors, u / (p : ℝ) :=
      Finset.sum_congr rfl hterm
    _ = ∑ Q ∈ S.image Nat.primeFactors, ∏ p ∈ Q, u / (p : ℝ) :=
      (Finset.sum_image (f := fun Q : Finset ℕ => ∏ p ∈ Q, u / (p : ℝ)) hinj).symm
    _ ≤ ∑ Q ∈ P.powerset, ∏ p ∈ Q, u / (p : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro Q hQ
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hQ
        exact Finset.mem_powerset.mpr (hP s hs)
      · intro Q hQ hnot
        exact Finset.prod_nonneg (fun p hp => div_nonneg hu (Nat.cast_nonneg _))
    _ = _ := (Finset.prod_one_add P).symm

theorem squarefree_weighted_reciprocal_le_exp (S P : Finset ℕ)
    (hS : ∀ s ∈ S, Squarefree s) (hP : ∀ s ∈ S, s.primeFactors ⊆ P)
    (u : ℝ) (hu : 0 ≤ u) :
    (∑ s ∈ S, u ^ s.primeFactors.card / (s : ℝ)) ≤
      Real.exp (u * ∑ p ∈ P, (p : ℝ)⁻¹) := by
  apply (squarefree_weighted_reciprocal_le_product S P hS hP u hu).trans
  calc
    _ ≤ ∏ p ∈ P, Real.exp (u / (p : ℝ)) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        positivity
      · intro p hp
        simpa only [add_comm] using Real.add_one_le_exp (u / (p : ℝ))
    _ = Real.exp (∑ p ∈ P, u / (p : ℝ)) := (Real.exp_sum P _).symm
    _ = _ := by simp only [div_eq_mul_inv, Finset.mul_sum]

end Ostmann

end OAI
