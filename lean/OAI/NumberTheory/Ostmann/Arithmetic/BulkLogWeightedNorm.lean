import OAI.NumberTheory.Ostmann.Arithmetic.BulkLogWeightedIntegrand

namespace OAI

/-! # Norm bounds after retaining the original bulk cutoffs -/

namespace Ostmann
open scoped Classical BigOperators

theorem BulkIntegrand.withLogCutoffs_norm_le {σ : Type*} [Fintype σ] {t : ℕ}
    (f : BulkIntegrand σ) (base : σ → ℝ) (S : Finset σ) (cb : ℝ)
    (slots : Fin t → List σ) (x : σ → ℝ) :
    ‖f.withLogCutoffs base S cb slots x‖ ≤ ‖f x‖ := by
  have hn : 0 ≤ ∏ j, bulkLogCutoffWeight (bulkLogValues base S x) cb (slots j) :=
    Finset.prod_nonneg (fun j _ => (bulkLogCutoffWeight_bounds _ _ _).1)
  have hle : (∏ j, bulkLogCutoffWeight (bulkLogValues base S x) cb (slots j)) ≤ 1 :=
    Finset.prod_le_one₀ (fun j _ => (bulkLogCutoffWeight_bounds _ _ _).1)
      (fun j _ => (bulkLogCutoffWeight_bounds _ _ _).2)
  change ‖((_ : ℝ) : ℂ) * f x‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hn]
  exact mul_le_of_le_one_left (norm_nonneg _) hle

end Ostmann

end OAI
