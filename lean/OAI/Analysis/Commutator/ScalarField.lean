import Mathlib
import OAI.Analysis.Commutator.DecomposableOperator

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma smul_measurable (z : ℂ) (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ) :
    ∀ ξ,AEStronglyMeasurable (fun a => (z • T a) ξ) μ := fun ξ => (hm ξ).const_smul z

lemma smul_field_bound (z : ℂ) (T : Ω → H →L[ℂ] H)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) : ∀ᵐ a ∂μ,‖z • T a‖≤‖z‖*b := by
  filter_upwards [hb] with a ha
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left ha (norm_nonneg z)

lemma operator_smul (z : ℂ) (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) :
    operator μ (fun a => z • T a) (smul_measurable μ z T hm)
      (smul_field_bound μ z T hb)=z • operator μ T hm hb := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [operator_ae μ (fun a => z • T a) (smul_measurable μ z T hm)
    (smul_field_bound μ z T hb) f,operator_ae μ T hm hb f,
    Lp.coeFn_smul z (operator μ T hm hb f)] with a h1 h2 h3
  change operator μ (fun a => z • T a) (smul_measurable μ z T hm)
    (smul_field_bound μ z T hb) f a=(z • operator μ T hm hb f) a
  rw [h1,h3]
  change z • T a (f a)=z • operator μ T hm hb f a
  rw [h2]

end Kadison.Decomposable

end

end
end

end OAI
