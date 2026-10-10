import OAI.Analysis.BoundedHochschild.FixedFactorizationLimits
import OAI.Analysis.BoundedHochschild.NormalFactorCandidates
import OAI.Analysis.BoundedHochschild.RightAveragingOrbit

namespace OAI

/-! All maps in a closed averaging orbit admit the same representation and
left factor as its initial map. Only the bounded right factor changes. -/

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def weakNormalOperatorFamily (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (F : M → WeakDual ℂ X) : M → (NormalGNS e →WOT[ℂ] NormalGNS e) :=
  fun a => normalGNSWeak e (F a)

lemma weakNormalOperatorFamily_continuous (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    Continuous (weakNormalOperatorFamily e) := by
  apply continuous_pi
  intro a
  exact (normalGNSWeak_continuous e).comp (continuous_apply a)

lemma weakNormalOperatorFamily_image (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (T : M →L[ℂ] M) (a : M) :
    weakNormalOperatorFamily e (weakOperatorImage e T) a =
      ContinuousLinearMapWOT.ofCLM (normalGNSRepresentation e (T a)) := by
  change ContinuousLinearMapWOT.ofCLM
    (normalGNSRepresentation e (e (e.symm (T a)))) = _
  rw [e.apply_symm_apply]

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem weakRightAverageOrbit_fixed_factorization (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L W : NormalGNS e →L[ℂ] K)
    (T : M →L[ℂ] M)
    (hT : ∀ a, normalGNSRepresentation e (T a) = L.adjoint.comp ((π a).comp W))
    (S : M →L[ℂ] M) (hS : weakOperatorImage e S ∈ weakRightAverageOrbit e T) :
    ∃ V : NormalGNS e →L[ℂ] K, ‖V‖ ≤ ‖W‖ ∧
      ∀ a, normalGNSRepresentation e (S a) = L.adjoint.comp ((π a).comp V) := by
  let B := {F : M → (NormalGNS e →WOT[ℂ] NormalGNS e) |
    ∃ V : NormalGNS e →L[ℂ] K, ‖V‖ ≤ ‖W‖ ∧
      ∀ a, F a = ContinuousLinearMapWOT.ofCLM (L.adjoint.comp ((π a).comp V))}
  have hclosed : IsClosed ((weakNormalOperatorFamily e) ⁻¹' B) :=
    (fixedFactorization_isClosed π L ‖W‖).preimage (weakNormalOperatorFamily_continuous e)
  have hsub : weakOperatorImage e '' rightAverageOrbit T ⊆
      (weakNormalOperatorFamily e) ⁻¹' B := by
    rintro F ⟨U, ⟨n, m, hm, rfl⟩, rfl⟩
    refine ⟨representedRightAverage π (normalGNSRepresentation e) m W,
      representedRightAverage_norm_le π (normalGNSRepresentation e) m hm W, ?_⟩
    intro a
    rw [weakNormalOperatorFamily_image]
    exact congrArg ContinuousLinearMapWOT.ofCLM
      (representedRightAverage_factorization π (normalGNSRepresentation e) T L W hT m a)
  obtain ⟨V, hV, he⟩ := closure_minimal hsub hclosed hS
  refine ⟨V, hV, fun a => ?_⟩
  have h := he a
  rw [weakNormalOperatorFamily_image] at h
  exact congrArg ContinuousLinearMapWOT.toCLM h

end BoundedHochschild.KadisonRingrose

end

end OAI
