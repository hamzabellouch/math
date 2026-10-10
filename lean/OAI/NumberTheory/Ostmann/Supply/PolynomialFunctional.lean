import OAI.NumberTheory.Ostmann.Supply.TensorOperators

namespace OAI

noncomputable section
namespace Ostmann.Supply.BivariateTruncation
open scoped BigOperators
open TensorOperators
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def mapCoefficients (φ : E→ₗ[ℂ]F) (c : (ℕ×ℕ)→₀E) : (ℕ×ℕ)→₀F :=
  ∑ij∈c.support,Finsupp.single ij (φ (c ij))

@[simp] theorem mapCoefficients_apply (φ : E→ₗ[ℂ]F) (c : (ℕ×ℕ)→₀E) (ij : ℕ×ℕ) :
    mapCoefficients φ c ij = φ (c ij) := by
  classical
  by_cases h : ij∈c.support
  · simp [mapCoefficients,Finsupp.single_apply,h]
  · have hz := Finsupp.notMem_support_iff.mp h
    simp [mapCoefficients,Finsupp.single_apply,h,hz]

theorem eval_mapCoefficients (φ : E→ₗ[ℂ]F) (c : (ℕ×ℕ)→₀E) (u v : ℂ) :
    eval (mapCoefficients φ c) u v = φ (eval c u v) := by
  rw [mapCoefficients,eval_sum]
  simp only [eval_single]
  simp only [eval,map_sum,map_smul]

def rectangularLinearMap (K : ℕ) : ((ℕ×ℕ)→₀E)→ₗ[ℂ]E :=
  Finsupp.lsum ℂ (fun ij => if ij.1≤K ∧ ij.2≤K then LinearMap.id else 0)

theorem rectangularLinearMap_apply (K : ℕ) (c : (ℕ×ℕ)→₀E) :
    rectangularLinearMap K c = rectangularTruncation c K := by
  classical
  simp only [rectangularLinearMap,Finsupp.lsum_apply,Finsupp.sum,rectangularTruncation,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ij hij
  split_ifs <;> rfl

@[simp] theorem rectangularTruncation_single (ij : ℕ×ℕ) (x : E) (K : ℕ) :
    rectangularTruncation (Finsupp.single ij x) K = if ij.1≤K ∧ ij.2≤K then x else 0 := by
  rw [←rectangularLinearMap_apply]
  unfold rectangularLinearMap
  rw [Finsupp.lsum_single]
  split_ifs <;> rfl

theorem rectangularTruncation_sum {α : Type*} (s : Finset α)
    (c : α→(ℕ×ℕ)→₀E) (K : ℕ) :
    rectangularTruncation (∑a∈s,c a) K = ∑a∈s,rectangularTruncation (c a) K := by
  simp only [←rectangularLinearMap_apply,map_sum]

theorem rectangularTruncation_mapCoefficients (φ : E→ₗ[ℂ]F)
    (c : (ℕ×ℕ)→₀E) (K : ℕ) :
    rectangularTruncation (mapCoefficients φ c) K = φ (rectangularTruncation c K) := by
  classical
  rw [mapCoefficients,rectangularTruncation_sum]
  simp only [rectangularTruncation_single]
  simp only [rectangularTruncation,Finset.sum_filter,map_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  split_ifs <;> simp

variable [CompleteSpace E]
theorem eq_of_eval_eq {c d : (ℕ×ℕ)→₀E} (h : ∀u v : ℂ,eval c u v=eval d u v) : c=d := by
  ext ij
  rw [←coefficientIntegral_eval c (by norm_num : (0:ℝ)<1) ij.1 ij.2,
    ←coefficientIntegral_eval d (by norm_num : (0:ℝ)<1) ij.1 ij.2]
  congr 1
  funext u
  congr 1
  funext v
  exact h u v

end Ostmann.Supply.BivariateTruncation

end

end OAI
