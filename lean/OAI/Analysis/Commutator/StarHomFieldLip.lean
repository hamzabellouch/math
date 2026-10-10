import Mathlib
import OAI.Analysis.Commutator.DecomposableAlgebra
import OAI.Analysis.Commutator.DecomposableNorm

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

namespace Kadison.Decomposable

variable {Ω H A : Type} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [IsFiniteMeasure μ] [CStarAlgebra A]

lemma representation_field_diff_bound
    (ρ : A →⋆ₐ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ))
    (T : A → Ω → H →L[ℂ] H)
    (hm : ∀ a ξ,AEStronglyMeasurable (fun x => T a x ξ) μ)
    (hb : ∀ a,∀ᵐ x ∂μ,‖T a x‖≤‖a‖)
    (he : ∀ a,ρ a=operator μ (T a) (hm a) (hb a)) (a b : A) :
    ∀ᵐ x ∂μ,‖T a x-T b x‖≤‖a-b‖ := by
  apply (operator_norm_le_iff_ae μ (fun x => T a x-T b x)
    (sub_measurable μ _ _ (hm a) (hm b)) (sub_bound μ _ _ (hb a) (hb b))
    (norm_nonneg (a-b))).mp
  rw [←operator_sub μ _ _ (hm a) (hm b) (hb a) (hb b),←he a,←he b,←map_sub]
  exact NonUnitalStarAlgHom.norm_apply_le ρ (a-b)

end Kadison.Decomposable

end

end
end

end OAI
