import OAI.Analysis.KadisonKastler.BoundaryFiniteIsomorphism
import OAI.Analysis.KadisonKastler.SpatialAssociatorTransport
import Mathlib.Analysis.Normed.Operator.Extend

namespace OAI

/-! # Spatial implementation of a vector-state preserving isomorphism

This is the representation-transport part of the modular-core isomorphism
argument. Changing the state itself still requires a separate construction.
-/

namespace KadisonKastler

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
  (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N) (Ω : H) (ξ : K)
  (hM : DenseRange (algebraVectorMap M Ω))
  (hN : DenseRange (algebraVectorMap N ξ))
  (hstate : ∀ a : Algebra M, inner ℂ Ω (a.val Ω) = inner ℂ ξ ((θ a).val ξ))

include hstate in
theorem statePreserving_norm (a : Algebra M) : ‖(θ a).val ξ‖ = ‖a.val Ω‖ := by
  have h := hstate (star a * a)
  change inner ℂ Ω (star a.val (a.val Ω)) =
    inner ℂ ξ ((θ (star a * a)).val ξ) at h
  have he : (θ (star a * a)).val = star (θ a).val * (θ a).val := by
    have hm : θ (star a * a) = θ (star a) * θ a := map_mul θ _ _
    have hs : θ (star a) = star (θ a) := map_star θ a
    rw [hm, hs]
    rfl
  rw [he, mul_apply_eq_comp] at h
  change inner ℂ Ω (a.val.adjoint (a.val Ω)) =
    inner ℂ ξ ((θ a).val.adjoint ((θ a).val ξ)) at h
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have hs : ‖a.val Ω‖ ^ 2 = ‖(θ a).val ξ‖ ^ 2 := by exact_mod_cast h
  nlinarith [norm_nonneg (a.val Ω), norm_nonneg ((θ a).val ξ)]

def statePreservingUnitary : H ≃ₗᵢ[ℂ] K :=
  θ.toAlgEquiv.toLinearEquiv.extendOfIsometry (algebraVectorMap M Ω) (algebraVectorMap N ξ)
    hM hN (statePreserving_norm θ Ω ξ hstate)

theorem statePreservingUnitary_algebraVector (a : Algebra M) :
    statePreservingUnitary θ Ω ξ hM hN hstate (a.val Ω) = (θ a).val ξ :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ a

theorem statePreservingUnitary_vector :
    statePreservingUnitary θ Ω ξ hM hN hstate Ω = ξ := by
  have h := statePreservingUnitary_algebraVector θ Ω ξ hM hN hstate 1
  rw [map_one] at h
  exact h

theorem statePreservingUnitary_intertwines (a : Algebra M) (x : H) :
    statePreservingUnitary θ Ω ξ hM hN hstate (a.val x) =
      (θ a).val (statePreservingUnitary θ Ω ξ hM hN hstate x) := by
  let V := statePreservingUnitary θ Ω ξ hM hN hstate
  apply hM.induction_on (p := fun x => V (a.val x) = (θ a).val (V x)) x
  · exact isClosed_eq (V.continuous.comp a.val.continuous)
      ((θ a).val.continuous.comp V.continuous)
  · intro b
    change V ((a * b).val Ω) = (θ a).val (V (b.val Ω))
    rw [statePreservingUnitary_algebraVector, statePreservingUnitary_algebraVector]
    simp only [map_mul]
    rfl

theorem statePreservingUnitary_conjugates (a : Algebra M) :
    (statePreservingUnitary θ Ω ξ hM hN hstate).conjStarAlgEquiv a.val = (θ a).val := by
  ext x
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, statePreservingUnitary_intertwines,
    LinearIsometryEquiv.apply_symm_apply]

end

end KadisonKastler

end OAI
