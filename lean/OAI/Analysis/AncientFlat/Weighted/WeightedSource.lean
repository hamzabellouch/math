import OAI.Analysis.AncientFlat.Evolution.SourceC0
import OAI.Analysis.AncientFlat.Weighted.WeightedSpatial

namespace OAI
noncomputable section
open scoped ZeroAtInfty BoundedContinuousFunction
namespace FlatWeighted
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem source_lift (γ α a : ℝ) (hγ : 0<γ) (hγ1 : γ<1/2)
    (hα : 0<α) (_ : α<1) (ha : 0<a) (_ : a≤1) :
    ∃ C : ℝ, 0<C ∧ ∀ (M : ℝ), 0≤M → ∀ f : V × ℝ → ℂ,
      YBound α (-2+4*γ) a M f →
      ∃ j : ℝ →ᵇ C₀(V,ℂ),
        (∀ τ z, j τ z=normalizedSource γ f τ z) ∧ ‖j‖≤M ∧
        ∀ τ : ℝ, ∀ x y : V, ‖j τ x-j τ y‖≤C*M*‖x-y‖^α := by
  refine ⟨1+2/a^α,by positivity,fun M hM f hf => ?_⟩
  obtain ⟨j,hj,hjn⟩ := hf.exists_source_bcf hγ1 hα ha hM
  refine ⟨j,hj,hjn,fun τ x y => ?_⟩
  rw [hj,hj,normalizedSource_eq_scaled,normalizedSource_eq_scaled]
  exact hf.scaled_spatial hα.le (by linarith) ha hM _ (Real.exp_pos _) x y
end FlatWeighted

end

end OAI
