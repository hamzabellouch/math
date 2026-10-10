import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

/-! The probability law of an explicitly weighted finite choice, viewed on the
natural numbers so that a single trajectory space works at all tree vertices. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

def finiteChoiceLaw (k : ℕ) (w : Fin k → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hw1 : (∑ i, w i) = 1) : ProbabilityMeasure ℕ :=
  ⟨∑ i, ENNReal.ofReal (w i) • Measure.dirac i.val, by
    constructor
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i), hw1, ENNReal.ofReal_one]⟩

theorem integrable_finiteChoiceLaw (k : ℕ) (w : Fin k → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hw1 : (∑ i, w i) = 1) (f : ℕ → ℝ) :
    Integrable f (finiteChoiceLaw k w hw hw1 : Measure ℕ) := by
  change Integrable f (∑ i : Fin k, ENNReal.ofReal (w i) • Measure.dirac i.val)
  apply integrable_finsetSum_measure.mpr
  intro i _
  exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

theorem integral_finiteChoiceLaw (k : ℕ) (w : Fin k → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hw1 : (∑ i, w i) = 1) (f : ℕ → ℝ) :
    ∫ a, f a ∂(finiteChoiceLaw k w hw hw1 : Measure ℕ) = ∑ i, w i * f i.val := by
  change ∫ a, f a ∂(∑ i : Fin k, ENNReal.ofReal (w i) • Measure.dirac i.val) = _
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw _),
      smul_eq_mul]
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

end CircleDomainRigidity

end

end OAI
