import Mathlib
import OAI.Probability.ThorpCompatibility.Model
import OAI.Probability.ThorpCompatibility.PermutationProbability

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
open Finset

lemma uniformMean_mono {α : Type*} [Fintype α] {f g : α → ℝ} (h : ∀ x, f x ≤ g x) :
    uniformMean f ≤ uniformMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => h x) (by positivity)

lemma uniformMean_sum {α β : Type*} [Fintype α] [Fintype β] (f : α → β → ℝ) :
    uniformMean (fun x => ∑ y, f x y) = ∑ y, uniformMean (fun x => f x y) := by
  simp only [uniformMean]
  rw [Finset.sum_comm, Finset.sum_div]

lemma uniformMean_const_mul {α : Type*} [Fintype α] (a : ℝ) (f : α → ℝ) :
    uniformMean (fun x => a * f x) = a * uniformMean f := by
  simp only [uniformMean, ← Finset.mul_sum, mul_div_assoc]

lemma uniformMean_indicator {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] :
    uniformMean (fun x => if P x then 1 else 0) = uniformProbability P := by
  rw [uniformProbability_def]
  simp [uniformMean]

end ThorpCompatibility

end OAI
