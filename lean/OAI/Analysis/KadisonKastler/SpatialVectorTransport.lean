import OAI.Analysis.KadisonKastler.StatePreservingSpatial

namespace OAI

/-! # Pulling a cyclic separating vector back through an intertwining unitary -/

namespace KadisonKastler

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
  (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N) (W : H ≃ₗᵢ[ℂ] K)
  (hW : ∀ (a : Algebra M) (x : H), W (a.val x) = (θ a).val (W x))
  (ξ : K)

include hW in
theorem spatialVectorTransport_action (a : Algebra M) :
    a.val (W.symm ξ) = W.symm ((θ a).val ξ) := by
  apply W.injective
  rw [hW, W.apply_symm_apply, W.apply_symm_apply]

include hW in
theorem spatialVectorTransport_state (a : Algebra M) :
    inner ℂ (W.symm ξ) (a.val (W.symm ξ)) = inner ℂ ξ ((θ a).val ξ) := by
  rw [spatialVectorTransport_action θ W hW ξ a]
  exact W.symm.inner_map_map _ _

include hW in
theorem spatialVectorTransport_cyclic (hξ : DenseRange (algebraVectorMap N ξ)) :
    DenseRange (algebraVectorMap M (W.symm ξ)) := by
  have hd := W.symm.surjective.denseRange.comp hξ W.symm.continuous
  apply hd.mono
  rintro _ ⟨a, rfl⟩
  refine ⟨θ.symm a, ?_⟩
  change (θ.symm a).val (W.symm ξ) = W.symm (a.val ξ)
  rw [spatialVectorTransport_action θ W hW ξ, θ.apply_symm_apply]

include hW in
theorem spatialVectorTransport_separating
    (hξ : Function.Injective (algebraVectorMap N ξ)) :
    Function.Injective (algebraVectorMap M (W.symm ξ)) := by
  intro a b hab
  apply θ.injective
  apply hξ
  change (θ a).val ξ = (θ b).val ξ
  have h := congrArg W hab
  change W (a.val (W.symm ξ)) = W (b.val (W.symm ξ)) at h
  simpa only [hW, W.apply_symm_apply] using h

end

end KadisonKastler

end OAI
