import OAI.NumberTheory.TwoPoint.Bounds.IndependentSampling

namespace OAI

/-! Finite pushforward identities, used to identify the actual two-selection
padding experiment with its three-point difference law. -/

namespace TwoPointCorrelations.FiniteLaw

open Finset
open scoped Classical

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]

lemma average_fibers (μ : FiniteLaw α) (g : α → β) (F : β → ℝ) :
    μ.average (fun x => F (g x)) = ∑ y, μ.probability (fun x => g x = y) * F y := by
  calc
    _ = μ.average (fun x => ∑ y, if g x = y then F y else 0) := by
      congr 1
      funext x
      simp
    _ = _ := by
      rw [average_sum]
      apply sum_congr rfl
      intro y _
      simp [average, probability, sum_mul, mul_ite, ite_mul]

lemma independent_average_map [DecidableEq ι] (μ : ι → FiniteLaw α)
    (ν : ι → FiniteLaw β) (g : ι → α → β)
    (hg : ∀ i y, (μ i).probability (fun x => g i x = y) = (ν i).weight y)
    (F : (ι → β) → ℝ) :
    (independent μ).average (fun x => F (fun i => g i (x i))) =
      (independent ν).average F := by
  rw [average_fibers]
  unfold average
  apply sum_congr rfl
  intro y _
  congr 1
  have he : (fun x : ι → α => (fun i => g i (x i)) = y) =
      (fun x => ∀ i, g i (x i) = y i) := by
    funext x
    exact propext funext_iff
  rw [he, independent_probability_all μ (fun i x => g i x = y i)]
  simp only [hg, independent]

noncomputable def dependentProduct (μ : FiniteLaw α) (ν : α → FiniteLaw β) :
    FiniteLaw (α × β) where
  weight x := μ.weight x.1 * (ν x.1).weight x.2
  nonneg x := mul_nonneg (μ.nonneg _) ((ν _).nonneg _)
  total := by
    simp only [Fintype.sum_prod_type, ← mul_sum, total, mul_one]

lemma average_dependentProduct (μ : FiniteLaw α) (ν : α → FiniteLaw β)
    (F : α × β → ℝ) :
    (μ.dependentProduct ν).average F =
      μ.average (fun x => (ν x).average (fun y => F (x, y))) := by
  simp only [average, dependentProduct, Fintype.sum_prod_type, mul_sum, mul_assoc]

end TwoPointCorrelations.FiniteLaw

end OAI
