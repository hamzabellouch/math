import OAI.Analysis.KadisonKastler.ProjectionFamilyLimits

namespace OAI

/-! # Closed quantitative constraints on projection families -/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def ProjectionFamilyAdmissible (J : H ≃ₗᵢ⋆[ℂ] H) (ξ η : H) (δ : ℝ)
    (S : Set (AlgebraProjection M)) : Prop :=
  (‖(1-modularQuadratic J (projectionFamilyRemainder S).val) ξ‖^2+
      ‖(1-modularQuadratic J (projectionFamilyRemainder S).val) η‖^2 ≤
    131072*‖(1-projectionFamilyPinching J S) η‖^2) ∧
  (‖(1-projectionFamilyPinching J S) ξ‖^2 ≤ δ*‖(1-projectionFamilyPinching J S) η‖^2)

theorem projectionFamilyAdmissible_iUnion {ι : Type*} [Preorder ι]
    [NeBot (atTop : Filter ι)] (J : H ≃ₗᵢ⋆[ℂ] H) (ξ η : H) (δ : ℝ)
    (S : ι → Set (AlgebraProjection M)) (hS : Monotone S)
    (h : ∀ i, ProjectionFamilyAdmissible J ξ η δ (S i)) :
    ProjectionFamilyAdmissible J ξ η δ (⋃ i, S i) := by
  have hQ (z : H) : Tendsto
      (fun i => ‖(1-modularQuadratic J (projectionFamilyRemainder (S i)).val) z‖^2) atTop
      (𝓝 (‖(1-modularQuadratic J (projectionFamilyRemainder (⋃ i, S i)).val) z‖^2)) := by
    have hc : Tendsto (fun _ : ι => z) atTop (𝓝 z) := tendsto_const_nhds
    have ht := (hc.sub (projectionFamilyQuadratic_tendsto J S hS z)).norm.pow 2
    simpa only [sub_apply,one_apply_eq_self] using ht
  have hR (z : H) : Tendsto
      (fun i => ‖(1-projectionFamilyPinching J (S i)) z‖^2) atTop
      (𝓝 (‖(1-projectionFamilyPinching J (⋃ i, S i)) z‖^2)) := by
    have hc : Tendsto (fun _ : ι => z) atTop (𝓝 z) := tendsto_const_nhds
    have ht := (hc.sub (projectionFamilyPinching_tendsto J S hS z)).norm.pow 2
    simpa only [sub_apply,one_apply_eq_self] using ht
  constructor
  · exact le_of_tendsto_of_tendsto ((hQ ξ).add (hQ η)) ((hR η).const_mul 131072)
      (Eventually.of_forall fun i => (h i).1)
  · exact le_of_tendsto_of_tendsto (hR ξ) ((hR η).const_mul δ)
      (Eventually.of_forall fun i => (h i).2)

end

end KadisonKastler

end OAI
