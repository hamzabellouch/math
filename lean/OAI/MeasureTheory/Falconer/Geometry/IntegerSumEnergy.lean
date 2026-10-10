import OAI.MeasureTheory.Falconer.Measures.PopularSquareMass
import OAI.MeasureTheory.Falconer.Graphs.BipartitePivot
import Mathlib.Combinatorics.Additive.Energy

namespace OAI

/-! Exact integer sum multiplicities and their additive energy. -/
namespace Falconer
open scoped Pointwise

noncomputable def integerSumMultiplicity (A B : Finset ℤ) (z : ℤ) : ℝ :=
  (((A ×ˢ B).filter fun p => p.1+p.2 = z).card : ℝ)

theorem integerSumMultiplicity_nonneg (A B : Finset ℤ) (z : ℤ) :
    0 ≤ integerSumMultiplicity A B z := Nat.cast_nonneg _

theorem integerSumMultiplicity_total (A B : Finset ℤ) :
    (∑ z ∈ A+B, integerSumMultiplicity A B z) = (A.card : ℝ)*(B.card : ℝ) := by
  unfold integerSumMultiplicity
  have h := Finset.card_eq_sum_card_image (fun p : ℤ × ℤ => p.1+p.2) (A ×ˢ B)
  rw [Finset.image_add_product,Finset.card_product] at h
  exact_mod_cast h.symm

theorem integerSumMultiplicity_energy (A B : Finset ℤ) :
    (∑ z ∈ A+B, (integerSumMultiplicity A B z)^2) = (Finset.addEnergy A B : ℝ) := by
  unfold integerSumMultiplicity
  exact_mod_cast (Finset.addEnergy_eq_sum_sq' A B).symm

theorem integerSumMultiplicity_le_left (A B : Finset ℤ) (z : ℤ) :
    integerSumMultiplicity A B z ≤ (A.card : ℝ) := by
  unfold integerSumMultiplicity
  have hm : Set.MapsTo Prod.fst
      (((A ×ˢ B).filter fun p => p.1+p.2 = z) : Set (ℤ × ℤ)) (A : Set ℤ) := by
    intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  have hi : Set.InjOn Prod.fst (((A ×ˢ B).filter fun p => p.1+p.2 = z) : Set (ℤ × ℤ)) := by
    intro p hp q hq he
    have h1 := (Finset.mem_filter.mp hp).2
    have h2 := (Finset.mem_filter.mp hq).2
    apply Prod.ext he
    change p.1 = q.1 at he
    omega
  exact_mod_cast Finset.card_le_card_of_injOn Prod.fst hm hi

theorem integerSumMultiplicity_restrict (A B C : Finset ℤ) :
    (∑ z ∈ C, integerSumMultiplicity A B z) =
      ∑ a ∈ A, ((integerNeighbors B (fun a b => a+b ∈ C) a).card : ℝ) := by
  unfold integerSumMultiplicity
  have h1 := Finset.sum_card_fiberwise_eq_card_filter (A ×ˢ B) C (fun p : ℤ × ℤ => p.1+p.2)
  have h2 : (((A ×ˢ B).filter fun p => p.1+p.2 ∈ C).card) =
      ∑ a ∈ A, (integerNeighbors B (fun a b => a+b ∈ C) a).card := by
    simp only [integerNeighbors,Finset.card_eq_sum_ones,Finset.sum_filter,Finset.sum_product]
  exact_mod_cast h1.trans h2

end Falconer

end OAI
