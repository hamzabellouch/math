import OAI.NumberTheory.Ostmann.Supply.TensorCoordinates

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
variable {ι : Type*} [DecidableEq ι]
variable {β : ι → Type*} [∀ i, Fintype (β i)]
variable {α : Type*}

def subsetRawEnergy (A : Finset α) (v : α → ∀ i, EuclideanSpace ℂ (β i))
    (t : Finset ι) : ℝ :=
  ‖∑ a ∈ A, tensorVector (fun i : t => v a i)‖^2

theorem subsetRawEnergy_nonneg (A : Finset α)
    (v : α → ∀ i, EuclideanSpace ℂ (β i)) (t : Finset ι) :
    0 ≤ subsetRawEnergy A v t := sq_nonneg _

theorem subsetRawEnergy_eq (A : Finset α)
    (v : α → ∀ i, EuclideanSpace ℂ (β i)) (t : Finset ι) :
    (subsetRawEnergy A v t : ℂ) =
      ∑ a ∈ A, ∑ b ∈ A, ∏ i ∈ t, inner ℂ (v a i) (v b i) := by
  calc
    (subsetRawEnergy A v t : ℂ) =
        ∑ a ∈ A, ∑ b ∈ A, ∏ i : t, inner ℂ (v a i) (v b i) :=
      (tensorGram_sum A (fun a => fun i : t => v a i)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.prod_coe_sort t (fun i => inner ℂ (v a i) (v b i))

theorem subsetRawEnergy_empty (A : Finset α)
    (v : α → ∀ i, EuclideanSpace ℂ (β i)) :
    subsetRawEnergy A v ∅ = (A.card : ℝ)^2 := by
  apply Complex.ofReal_injective
  rw [subsetRawEnergy_eq]
  simp
  ring

variable [Fintype ι]

theorem tensorKernel_expansion (A : Finset α)
    (v : α → ∀ i, EuclideanSpace ℂ (β i)) (κ w : ι → ℝ) :
    (∑ a ∈ A, ∑ b ∈ A,
      ∏ i, ((w i : ℂ) * inner ℂ (v a i) (v b i) + κ i)) =
    ∑ t : Finset ι, ((∏ i ∈ t, w i) * ∏ i ∈ tᶜ, κ i : ℝ) * subsetRawEnergy A v t := by
  push_cast
  simp_rw [Fintype.prod_add]
  simp_rw [Finset.sum_comm (s := A) (t := Finset.univ)]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [subsetRawEnergy_eq, Finset.mul_sum, Finset.prod_mul_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem tensorKernel_lower (A : Finset α)
    (v : α → ∀ i, EuclideanSpace ℂ (β i)) (κ w : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (hw : ∀ i, 0 ≤ w i) :
    (A.card : ℝ)^2 * (∏ i, κ i) ≤
      (∑ a ∈ A, ∑ b ∈ A,
        ∏ i, ((w i : ℂ) * inner ℂ (v a i) (v b i) + κ i)).re := by
  rw [tensorKernel_expansion]
  simp only [Complex.ofReal_re]
  have hn (t : Finset ι) :
      0 ≤ ((∏ i ∈ t, w i) * ∏ i ∈ tᶜ, κ i) * subsetRawEnergy A v t := by
    exact mul_nonneg (mul_nonneg (Finset.prod_nonneg fun i _ => hw i)
      (Finset.prod_nonneg fun i _ => hκ i)) (subsetRawEnergy_nonneg A v t)
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun t : Finset ι => ((∏ i ∈ t, w i) * ∏ i ∈ tᶜ, κ i) * subsetRawEnergy A v t)
    (fun t _ => hn t) (Finset.mem_univ (∅ : Finset ι))
  simpa only [Finset.prod_empty, one_mul, Finset.compl_empty,
    subsetRawEnergy_empty, mul_one, mul_comm] using h

end Ostmann.Supply

end

end OAI
