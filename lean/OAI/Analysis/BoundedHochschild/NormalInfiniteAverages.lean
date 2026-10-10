import OAI.Analysis.BoundedHochschild.InfiniteRepresentedAverages
import OAI.Analysis.BoundedHochschild.NormalFactorCandidates
import OAI.Analysis.BoundedHochschild.NormalGNSConvergence

namespace OAI

/-! Infinite normalized right averages remain valued in the original algebra.
The proof realizes their lifted strong limits through the closed represented
algebra balls, without a normality assumption on the auxiliary representation. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {I K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma normalGNS_row_limit (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (m : I → M)
    (hlim : PredualTendsto e (fun s : Finset I => ∑ i ∈ s, m i * star (m i)) atTop 1)
    (ξ : NormalGNS e) :
    Tendsto (fun s : Finset I => inner ℂ ξ
      (normalGNSRepresentation e (∑ i ∈ s, m i * star (m i)) ξ))
      atTop (𝓝 (inner ℂ ξ ξ)) := by
  simpa only [map_one, one_apply_eq_self] using normalGNS_predual_tendsto e hlim ξ ξ

theorem normal_infinite_average_realize (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L W : NormalGNS e →L[ℂ] K)
    (T : M →L[ℂ] M)
    (hT : ∀ a, normalGNSRepresentation e (T a) = L.adjoint.comp ((π a).comp W))
    (m : I → M) (hm : ∀ s : Finset I, ∑ i ∈ s, m i * star (m i) ≤ 1)
    (hlim : PredualTendsto e (fun s : Finset I => ∑ i ∈ s, m i * star (m i)) atTop 1) :
    ∃ S : M →L[ℂ] M, ‖S‖ ≤ ‖L‖ * ‖W‖ ∧ ∀ a,
      normalGNSRepresentation e (S a) = L.adjoint.comp ((π a).comp
        (infiniteRepresentedRightAverage π (normalGNSRepresentation e) m hm W)) := by
  let W₀ := ContinuousLinearMapWOT.ofCLM W
  have hW₀ : W₀ ∈ factorCandidates (normalGNSRepresentation e) π L ‖W‖ := by
    apply mem_factorCandidates_of_range _ (normalGNSRepresentation_injective e) π L le_rfl
    exact fun a => ⟨T a, hT a⟩
  have hmem := infiniteRepresentedRightAverage_mem_closed_orbit π (normalGNSRepresentation e)
    m hm (normalGNS_row_limit e m hlim) W₀
  have hW₁ := closedRepresentedAveragingOrbit_subset_candidates (normalGNSRepresentation e)
    (normalGNSRepresentation_injective e) (normalGNS_representation_ball_closed e)
    π L (norm_nonneg W) hW₀ hmem
  exact factorCandidates_realize (normalGNSRepresentation e) (normalGNSRepresentation_injective e)
    π L (norm_nonneg W) hW₁

end BoundedHochschild.KadisonRingrose

end

end OAI
