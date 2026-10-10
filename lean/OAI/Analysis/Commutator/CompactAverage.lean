import Mathlib
import OAI.Analysis.Commutator.StrongContinuity
import OAI.Analysis.Commutator.WeakOperatorIntegral

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace

open MeasureTheory MeasureTheory.Measure

namespace Kadison.CompactAverage

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : G →* (H ≃ₗᵢ[ℂ] H)) (hU : ∀ x : H, Continuous fun g => U g x)

variable (Y : H →L[ℂ] H)

def conjugate (g : G) : H →L[ℂ] H := (U g).conjStarAlgEquiv Y

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
include hU in
lemma conjugate_continuous (x : H) : Continuous fun g => conjugate U Y g x := by
  have hi : Continuous fun g => (U g).symm x := by
    simpa only [Function.comp_def, map_inv,LinearIsometryEquiv.coe_inv] using (hU x).comp continuous_inv
  have hj := StrongContinuity.joint (fun g => (U g).toLinearIsometry) hU
  exact hj.comp (continuous_id.prodMk (Y.continuous.comp hi))

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
lemma conjugate_norm (g : G) : ‖conjugate U Y g‖ = ‖Y‖ := by
  exact StarAlgEquiv.norm_map (U g).conjStarAlgEquiv Y

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
lemma conjugate_covariant (g k : G) :
    (U g : H →L[ℂ] H) * conjugate U Y k = conjugate U Y (g*k) * (U g : H →L[ℂ] H) := by
  ext x
  simp [conjugate,mul_apply_eq_comp,map_mul,LinearIsometryEquiv.mul_def]

include hU in
theorem exists_average (μ : Measure G) [IsProbabilityMeasure μ] [IsMulLeftInvariant μ] :
    ∃ V : H →L[ℂ] H, ‖V‖ ≤ ‖Y‖ ∧
      (∀ g, V * (U g : H →L[ℂ] H) = (U g : H →L[ℂ] H) * V) ∧
      (∀ x y, inner ℂ (V x) y = ∫ g, inner ℂ (conjugate U Y g x) y ∂μ) := by
  have hI : ∀ x y, Integrable (fun g => inner ℂ (conjugate U Y g x) y) μ := by
    intro x y
    exact ((conjugate_continuous U hU Y x).inner continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  obtain ⟨V,hb,hV⟩ := WeakOperatorIntegral.exists_integral μ (conjugate U Y) hI ‖Y‖
    (norm_nonneg _) (fun g => (conjugate_norm U Y g).le)
  refine ⟨V,hb,?_,hV⟩
  intro g
  ext x
  apply ext_inner_right ℂ
  intro y
  simp only [mul_apply_eq_comp]
  rw [← ContinuousLinearMap.adjoint_inner_right (U g : H →L[ℂ] H),hV,hV]
  have hc : ∀ k, inner ℂ (conjugate U Y k x) ((U g : H →L[ℂ] H).adjoint y) =
      inner ℂ (conjugate U Y (g*k) ((U g) x)) y := by
    intro k
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact congrArg (fun A : H →L[ℂ] H => inner ℂ (A x) y) (conjugate_covariant U Y g k)
  simp_rw [hc]
  exact (integral_mul_left_eq_self (fun k => inner ℂ (conjugate U Y k ((U g) x)) y) g).symm

end Kadison.CompactAverage

end

end
end

end OAI
