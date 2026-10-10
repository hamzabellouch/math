import OAI.GroupTheory.PolycyclicRecognition.Analysis.CayleyHarmonic

namespace OAI

/-! # Reverse energy from a finitely supported Cayley cutoff -/
noncomputable section
namespace PolycyclicRecognition
open Finset
variable {G : Type*} [Group G] [DecidableEq G]

theorem cayley_cutoff_dirichlet_bound
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S) (A F : Finset G) (hAF : A ⊆ F)
    (f η : G → ℝ) (hf : CayleyHarmonic S f)
    (hη : ∀ x ∈ F, η x ≠ 0 → ∀ s ∈ S, x * s ∈ F)
    (hηA : ∀ x ∈ A, η x = 1) (hAN : ∀ x ∈ A, ∀ s ∈ S, x * s ∈ F)
    (L : ℝ) (hL : 0 ≤ L) (hgrad : ∀ x ∈ F, ∀ s ∈ S, |η (x * s) - η x| ≤ L) :
    cayleyDirichletEnergy S A f ≤ 4 * (S.card : ℝ) * L ^ 2 * ∑ x ∈ F, f x ^ 2 := by
  have hlo : cayleyDirichletEnergy S A f ≤
      ∑ x ∈ F, ∑ y ∈ F, cayleyAdjacencyWeight S x y *
        (η x ^ 2 * (f y - f x) ^ 2) := by
    calc
      _ = ∑ x ∈ A, ∑ y ∈ F, cayleyAdjacencyWeight S x y *
          (η x ^ 2 * (f y - f x) ^ 2) := by
        apply sum_congr rfl
        intro x hx
        rw [hηA x hx]
        simp only [one_pow, one_mul]
        exact (finite_cayley_neighbor_sum S F x (fun y => (f y - f x) ^ 2) (hAN x hx)).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hAF (fun x _ _ => sum_nonneg (fun y _ =>
        mul_nonneg (cayleyAdjacencyWeight_nonneg S x y) (mul_nonneg (sq_nonneg _) (sq_nonneg _))))
  have hhi : (∑ x ∈ F, ∑ y ∈ F, cayleyAdjacencyWeight S x y *
      (f x ^ 2 * (η y - η x) ^ 2)) ≤
      (S.card : ℝ) * L ^ 2 * ∑ x ∈ F, f x ^ 2 := by
    calc
      _ ≤ ∑ x ∈ F, ∑ s ∈ S, f x ^ 2 * (η (x * s) - η x) ^ 2 := by
        apply sum_le_sum
        intro x _
        exact finite_cayley_neighbor_sum_le S F x
          (fun y => f x ^ 2 * (η y - η x) ^ 2)
          (fun y => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ ≤ ∑ x ∈ F, ∑ _s ∈ S, f x ^ 2 * L ^ 2 := by
        apply sum_le_sum
        intro x hx
        apply sum_le_sum
        intro s hs
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hL).2 (hgrad x hx s hs)
      _ = _ := by
        simp only [sum_const, nsmul_eq_mul, ← mul_sum, ← sum_mul]
        ring
  exact hlo.trans ((cayley_finite_cutoff_energy S hS F f η hf hη).trans
    ((mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 4)).trans_eq (by ring)))

end PolycyclicRecognition

end

end OAI
