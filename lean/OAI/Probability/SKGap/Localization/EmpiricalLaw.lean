import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
namespace SKGap

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def empiricalLaw (y : ι → ℝ) : ProbabilityMeasure ℝ :=
  ⟨(Fintype.card ι : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (y i), ⟨by
    rw [Measure.smul_apply, Measure.finsetSum_apply]
    simp only [Measure.dirac_apply_of_mem (mem_univ _), Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast ((Fintype.card_pos (α := ι)).ne')) (by simp)⟩⟩

lemma empiricalLaw_coe (y : ι → ℝ) : (empiricalLaw y : Measure ℝ) =
    (Fintype.card ι : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (y i) := rfl

lemma integrable_empiricalLaw (y : ι → ℝ) (f : ℝ → ℝ) : Integrable f (empiricalLaw y : Measure ℝ) := by
  rw [empiricalLaw_coe]
  apply Integrable.smul_measure
  · exact integrable_finsetSum_measure.mpr (fun i _ => integrable_dirac (by simp))
  · exact ENNReal.inv_ne_top.mpr (by exact_mod_cast ((Fintype.card_pos (α := ι)).ne'))

lemma integral_empiricalLaw (y : ι → ℝ) (f : ℝ → ℝ) :
    (∫ x, f x ∂empiricalLaw y) = (Fintype.card ι : ℝ)⁻¹ * ∑ i, f (y i) := by
  rw [empiricalLaw_coe, integral_smul_measure,
    integral_finsetSum_measure (fun i _ => integrable_dirac (by simp))]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]

lemma card_mul_integral_empiricalLaw (y : ι → ℝ) (f : ℝ → ℝ) :
    (Fintype.card ι : ℝ)*(∫ x, f x ∂empiricalLaw y) = ∑ i, f (y i) := by
  rw [integral_empiricalLaw, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast (Fintype.card_pos (α := ι)).ne'), one_mul]

lemma continuous_empiricalLaw : Continuous (empiricalLaw (ι := ι)) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  simp_rw [integral_empiricalLaw]
  fun_prop

end SKGap
end
end

end OAI
