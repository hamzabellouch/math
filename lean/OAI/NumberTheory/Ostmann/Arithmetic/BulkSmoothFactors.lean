import OAI.NumberTheory.Ostmann.Arithmetic.BulkFourierFactors
import OAI.NumberTheory.Ostmann.Arithmetic.BulkNodeFactors

namespace OAI

/-! # Full smooth bulk-coordinate factor and its finite variation budget -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def bulkSmoothFactors {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) :
    Fin (2 ^ n + (T.bulkNodePolynomials value i L R).length) → ClippedPolynomialFactor :=
  Fin.append (bulkFourierFactors value i T L R ψ X lo hi hlo hhi)
    (bulkNodeFactors value i T L R φ G B D hB hD hφ hlip)

theorem bulkSmoothFactors_value {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (hT : T.CompensationAbsent i)
    (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (p : ℝ) :
    smoothPolynomialWeight (bulkSmoothFactors value i T L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip)
      (p : ℝ) = realValueSmoothWeight (Function.update value i p) T ψ X lo hi hlo hhi φ G
        (L.eval (p : ℝ)) (R.eval (p : ℝ)) := by
  simp only [smoothPolynomialWeight, bulkSmoothFactors, Fin.prod_univ_add,
    Fin.append_left, Fin.append_right]
  exact congrArg₂ (· * ·) (bulkFourierFactors_value value i T hT L R ψ X lo hi hlo hhi p)
    (bulkNodeFactors_value value i T hT L R φ G B D hB hD hφ hlip hout p)

theorem bulkSmoothFactors_budget {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : T.Frequencies (fun s => |(s : ℝ)| ≤ V)) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) :
    smoothPolynomialBudget (bulkSmoothFactors value i T L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip) ≤
      movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1) := by
  change smoothPolynomialBudget (Fin.append _ _) ≤ _
  simp only [smoothPolynomialBudget, Fin.prod_univ_add, Fin.append_left, Fin.append_right]
  change smoothPolynomialBudget (bulkFourierFactors value i T L R ψ X lo hi hlo hhi) *
    smoothPolynomialBudget (bulkNodeFactors value i T L R φ G B D hB hD hφ hlip) ≤ _
  rw [bulkNodeFactors_budget]
  apply mul_le_mul_of_nonneg_right (bulkFourierFactors_budget value i T L R ψ X lo hi V hlo hhi hV)
  have hE := Real.one_le_exp (show (0 : ℝ) ≤ 2 by norm_num)
  positivity

/-- Specialization back to the exact natural-prime samples. -/
theorem bulkSmoothFactors_nat_value {σ : Type*} (value : σ → ℕ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (hT : T.CompensationAbsent i)
    (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (p : ℕ) :
    smoothPolynomialWeight (bulkSmoothFactors (fun j => (value j : ℝ)) i T L R ψ X lo hi
      hlo hhi φ G B D hB hD hφ hlip) (p : ℝ) =
      movingRealSmoothWeight (Function.update value i p) T ψ X lo hi hlo hhi φ G
        (L.eval (p : ℝ)) (R.eval (p : ℝ)) := by
  have hv : Function.update (fun j => (value j : ℝ)) i (p : ℝ) =
      (fun j => (Function.update value i p j : ℝ)) := by
    funext j
    by_cases hj : j = i
    · subst j; simp only [Function.update_self]
    · simp only [Function.update_of_ne hj]
  rw [bulkSmoothFactors_value (fun j => (value j : ℝ)) i T hT L R ψ X lo hi hlo hhi
    φ G B D hB hD hφ hlip hout (p : ℝ), hv, realValueSmoothWeight_nat]

end Ostmann

end OAI
