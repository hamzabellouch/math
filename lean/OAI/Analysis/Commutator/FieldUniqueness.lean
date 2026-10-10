import Mathlib
import OAI.Analysis.Commutator.DecomposableAlgebra
import OAI.Analysis.Commutator.DecomposableNorm

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

lemma field_eq_ae_of_operator_eq (T S : Ω → H →L[ℂ] H)
    (hT : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    (hS : ∀ ξ,AEStronglyMeasurable (fun a => S a ξ) μ)
    {b c : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hc : ∀ᵐ a ∂μ,‖S a‖≤c)
    (he : operator μ T hT hb=operator μ S hS hc) : T=ᵐ[μ]S := by
  have hz : operator μ (fun a => T a-S a) (sub_measurable μ T S hT hS)
      (sub_bound μ T S hb hc)=0 := by
    rw [←operator_sub μ T S hT hS hb hc,he,sub_self]
  have hn := (operator_norm_le_iff_ae μ (fun a => T a-S a)
    (sub_measurable μ T S hT hS) (sub_bound μ T S hb hc) (by norm_num : (0:ℝ)≤0)).mp
    (by rw [hz]; simp)
  filter_upwards [hn] with a ha
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm ha (norm_nonneg _)))

end Kadison.Decomposable

end

end
end

end OAI
