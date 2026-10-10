import OAI.NumberTheory.Ostmann.Arithmetic.BulkLogWeightedKernelPairComparison
import OAI.NumberTheory.Ostmann.Arithmetic.RealBulkKernelPair

namespace OAI

/-! # Bounded measurable bulk integrands retaining the initial cutoffs -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem continuous_bulkLogCutoffWeight {σ A : Type*} [TopologicalSpace A]
    (value : A → σ → ℝ) (hvalue : ∀ i, Continuous (fun x => value x i))
    (cb : ℝ) (slots : List σ) :
    Continuous (fun x => (bulkLogCutoffWeight (value x) cb slots : ℂ)) := by
  obtain ⟨D, hD, hlip⟩ := logCellProfile_lipschitz
  let f := logCutoffPolynomialFactor Polynomial.X logCellProfile cb 1 D zero_le_one hD
    (fun x => by rw [abs_of_nonneg (logCellProfile_nonneg x)]; exact logCellProfile_le_one x) hlip
  have hf : Continuous (fun z => (positiveLogCutoff logCellProfile cb z : ℂ)) := by
    apply f.continuous_value.congr
    intro z
    simpa only [f, Polynomial.eval_X] using
      logCutoffPolynomialFactor_value Polynomial.X logCellProfile cb 1 D zero_le_one hD
        (fun x => by rw [abs_of_nonneg (logCellProfile_nonneg x)]; exact logCellProfile_le_one x)
        hlip logCellProfile_zero_outside z
  exact hf.comp (continuous_realSlotProduct value hvalue slots)

noncomputable def BulkIntegrand.withLogCutoffs {σ : Type*} [Fintype σ] {t : ℕ}
    (f : BulkIntegrand σ) (base : σ → ℝ) (S : Finset σ) (cb : ℝ)
    (slots : Fin t → List σ) : BulkIntegrand σ where
  toFun x := ((∏ j, bulkLogCutoffWeight (bulkLogValues base S x) cb (slots j) : ℝ) : ℂ) * f x
  measurable := by
    have hcont : Continuous (fun x =>
        ∏ j, (bulkLogCutoffWeight (bulkLogValues base S x) cb (slots j) : ℂ)) :=
      continuous_finsetProd _ (fun j _ => continuous_bulkLogCutoffWeight
        (bulkLogValues base S) (continuous_bulkLogValues base S) cb (slots j))
    convert hcont.measurable.mul f.measurable using 1
    ext x
    exact congrArg (fun z : ℂ => z * f x) (Complex.ofReal_prod _ _)
  bounded := by
    obtain ⟨C, hC, hf⟩ := f.bounded
    refine ⟨C, hC, fun x => ?_⟩
    have hnonneg : 0 ≤ ∏ j, bulkLogCutoffWeight (bulkLogValues base S x) cb (slots j) :=
      Finset.prod_nonneg (fun j _ => (bulkLogCutoffWeight_bounds _ _ _).1)
    have hle : (∏ j, bulkLogCutoffWeight (bulkLogValues base S x) cb (slots j)) ≤ 1 :=
      Finset.prod_le_one₀ (fun j _ => (bulkLogCutoffWeight_bounds _ _ _).1)
        (fun j _ => (bulkLogCutoffWeight_bounds _ _ _).2)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hnonneg]
    exact (mul_le_of_le_one_left (norm_nonneg _) hle).trans (hf x)

end Ostmann

end OAI
