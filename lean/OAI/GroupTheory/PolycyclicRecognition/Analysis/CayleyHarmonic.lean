import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CayleyPoincare
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteGraphCaccioppoli

namespace OAI

/-! # Harmonicity and the finite Cayley cutoff estimate -/
noncomputable section
namespace PolycyclicRecognition
open Finset
variable {G : Type*} [Group G] [DecidableEq G]

def CayleyHarmonic (S : Finset G) (f : G → ℝ) : Prop :=
  ∀ x, ∑ s ∈ S, (f (x * s) - f x) = 0

def cayleyAdjacencyWeight (S : Finset G) (x y : G) : ℝ :=
  if x⁻¹ * y ∈ S then 1 else 0

theorem cayleyAdjacencyWeight_symm (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (x y : G) : cayleyAdjacencyWeight S x y = cayleyAdjacencyWeight S y x := by
  have he : x⁻¹ * y ∈ S ↔ y⁻¹ * x ∈ S := by
    constructor <;> intro h
    · simpa only [mul_inv_rev, inv_inv] using hS _ h
    · simpa only [mul_inv_rev, inv_inv] using hS _ h
  simp only [cayleyAdjacencyWeight, he]

theorem cayleyAdjacencyWeight_nonneg (S : Finset G) (x y : G) :
    0 ≤ cayleyAdjacencyWeight S x y := by
  unfold cayleyAdjacencyWeight
  split_ifs <;> norm_num

theorem finite_cayley_neighbor_sum (S F : Finset G) (x : G) (v : G → ℝ)
    (hF : ∀ s ∈ S, x * s ∈ F) :
    (∑ y ∈ F, cayleyAdjacencyWeight S x y * v y) = ∑ s ∈ S, v (x * s) := by
  have he : F.filter (fun y => x⁻¹ * y ∈ S) = S.image (fun s => x * s) := by
    ext y
    simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨_, hy⟩
      exact ⟨x⁻¹ * y, hy, mul_inv_cancel_left x y⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨hF s hs, by simpa only [inv_mul_cancel_left] using hs⟩
  simp only [cayleyAdjacencyWeight, ite_mul, one_mul, zero_mul]
  rw [← sum_filter, he, sum_image]
  intro s _ t _ hst
  exact mul_left_cancel hst

theorem finite_cayley_neighbor_sum_le (S F : Finset G) (x : G) (v : G → ℝ)
    (hv : ∀ y, 0 ≤ v y) :
    (∑ y ∈ F, cayleyAdjacencyWeight S x y * v y) ≤ ∑ s ∈ S, v (x * s) := by
  let B := F ∪ S.image (fun s => x * s)
  calc
    _ ≤ ∑ y ∈ B, cayleyAdjacencyWeight S x y * v y :=
      sum_le_sum_of_subset_of_nonneg subset_union_left
        (fun y _ _ => mul_nonneg (cayleyAdjacencyWeight_nonneg S x y) (hv y))
    _ = _ := finite_cayley_neighbor_sum S B x v (fun s hs =>
      mem_union_right F (mem_image.mpr ⟨s, hs, rfl⟩))

theorem cayley_finite_cutoff_energy
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S) (F : Finset G)
    (f η : G → ℝ) (hf : CayleyHarmonic S f)
    (hη : ∀ x ∈ F, η x ≠ 0 → ∀ s ∈ S, x * s ∈ F) :
    (∑ x ∈ F, ∑ y ∈ F, cayleyAdjacencyWeight S x y *
      (η x ^ 2 * (f y - f x) ^ 2)) ≤
    4 * ∑ x ∈ F, ∑ y ∈ F, cayleyAdjacencyWeight S x y *
      (f x ^ 2 * (η y - η x) ^ 2) := by
  have hh (x : F) (hx : η x ≠ 0) :
      (∑ y : F, cayleyAdjacencyWeight S x y * (f y - f x)) = 0 := by
    rw [sum_coe_sort F (fun y : G => cayleyAdjacencyWeight S x y * (f y - f x)),
      finite_cayley_neighbor_sum S F x (fun y => f y - f x)
      (hη x x.property hx)]
    exact hf x
  have h := finite_graph_caccioppoli
    (fun x y : F => cayleyAdjacencyWeight S x y)
    (fun x y => cayleyAdjacencyWeight_symm S hS x y)
    (fun x y => cayleyAdjacencyWeight_nonneg S x y)
    (fun x : F => f x) (fun x : F => η x) hh
  have he (u : G → G → ℝ) : (∑ x : F, ∑ y : F, u x y) =
      ∑ x ∈ F, ∑ y ∈ F, u x y := by
    calc
      _ = ∑ x : F, ∑ y ∈ F, u x y := by
        apply sum_congr rfl
        intro x _
        exact sum_coe_sort F (fun y : G => u x y)
      _ = _ := sum_coe_sort F (fun x : G => ∑ y ∈ F, u x y)
  dsimp only [weightedEdgeSum] at h
  rw [he (fun x y => cayleyAdjacencyWeight S x y * (η x ^ 2 * (f y - f x) ^ 2)),
    he (fun x y => cayleyAdjacencyWeight S x y * (f x ^ 2 * (η y - η x) ^ 2))] at h
  exact h

end PolycyclicRecognition

end

end OAI
