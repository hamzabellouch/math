import OAI.Analysis.KadisonKastler.CornerHomogeneityApplication
import OAI.Analysis.KadisonKastler.SpatialVectorTransport
import OAI.Analysis.KadisonKastler.StateBicentralizerTests

namespace OAI

/-! # Vector-state comparison under a spatial algebra isomorphism -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

theorem intertwines_of_unitaryConj {N : VonNeumannAlgebra H}
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra N) (u : unitary (H →L[ℂ] H))
    (he : ∀ a : Algebra M, unitaryConj u a.val=(e a).val) (a : Algebra M) (x : H) :
    Unitary.linearIsometryEquiv u (a.val x)=(e a).val (Unitary.linearIsometryEquiv u x) := by
  have h := congrArg (fun T : H →L[ℂ] H => T*(u : H →L[ℂ] H)) (he a)
  change ((u : H →L[ℂ] H)*a.val*star (u : H →L[ℂ] H))*(u : H →L[ℂ] H)=
    (e a).val*(u : H →L[ℂ] H) at h
  simp only [mul_assoc,u.property.1,mul_one] at h
  exact congrArg (fun T : H →L[ℂ] H => T x) h

theorem functional_norm_eq_of_starEquiv
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra N)
    (φ : Algebra M →L[ℂ] ℂ) (ψ : Algebra N →L[ℂ] ℂ)
    (he : ∀ a, φ a=ψ (e a)) : ‖φ‖=‖ψ‖ := by
  have hn (a : Algebra M) : ‖e a‖=‖a‖ :=
    NonUnitalStarAlgHom.norm_map e.toStarAlgHom e.injective a
  have hn' (b : Algebra N) : ‖e.symm b‖=‖b‖ :=
    NonUnitalStarAlgHom.norm_map e.symm.toStarAlgHom e.symm.injective b
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg ψ)
    intro a
    rw [he]
    simpa only [hn] using ψ.le_opNorm (e a)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg φ)
    intro b
    have hh : ψ b=φ (e.symm b) := by rw [he,e.apply_symm_apply]
    rw [hh]
    simpa only [hn'] using φ.le_opNorm (e.symm b)

variable (e : Algebra M ≃⋆ₐ[ℂ] Algebra N) (W : H ≃ₗᵢ[ℂ] K)
  (hW : ∀ (a : Algebra M) (x : H), W (a.val x)=(e a).val (W x))

include hW in
theorem spatial_vectorFunctional (ξ : K) (a : Algebra M) :
    vectorFunctional (W.symm ξ) a=vectorFunctional ξ (e a) :=
  spatialVectorTransport_state e W hW ξ a

include hW in
theorem spatial_stateCommutator_norm (ξ : K) (a : Algebra M) :
    ‖vectorStateCommutator (W.symm ξ) a‖=‖vectorStateCommutator ξ (e a)‖ := by
  apply functional_norm_eq_of_starEquiv e
  intro b
  change vectorFunctional (W.symm ξ) (a*b-b*a)=vectorFunctional ξ (e a*e b-e b*e a)
  rw [spatial_vectorFunctional e W hW,map_sub e,map_mul e,map_mul e]

include hW in
theorem FaithfulVectorStateHomogeneity.spatial_transport
    (hhom : FaithfulVectorStateHomogeneity M) : FaithfulVectorStateHomogeneity N := by
  intro ξ ζ hξ hζ hsξ hsζ ε hε
  have hsξ' := spatialVectorTransport_separating e W hW ξ hsξ
  have hsζ' := spatialVectorTransport_separating e W hW ζ hsζ
  obtain ⟨u,hu⟩ := hhom (W.symm ξ) (W.symm ζ)
    ((W.symm.norm_map ξ).trans hξ) ((W.symm.norm_map ζ).trans hζ) hsξ' hsζ' ε hε
  let v : unitary (Algebra N) := Unitary.map (StarMonoidHom.ofClass e) u
  refine ⟨v,?_⟩
  have hn : ‖sandwichFunctional (vectorFunctional (W.symm ξ)) u.val-
      vectorFunctional (W.symm ζ)‖ =
      ‖sandwichFunctional (vectorFunctional ξ) v.val-vectorFunctional ζ‖ := by
    apply functional_norm_eq_of_starEquiv e
    intro a
    change vectorFunctional (W.symm ξ) (star u.val*a*u.val)-vectorFunctional (W.symm ζ) a =
      vectorFunctional ξ (star v.val*e a*v.val)-vectorFunctional ζ (e a)
    rw [spatial_vectorFunctional e W hW,spatial_vectorFunctional e W hW,
      map_mul e,map_mul e,map_star e]
    rfl
  exact hn ▸ hu

end

end KadisonKastler

end OAI
