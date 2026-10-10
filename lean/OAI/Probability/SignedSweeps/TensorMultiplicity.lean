import OAI.Probability.SignedSweeps.WordTensorBasis

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {E F L G : Type*} [Monoid G]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    [AddCommGroup L] [Module ℂ L]

def tensorContract (φ : Module.Dual ℂ F) : E ⊗[ℂ] F →ₗ[ℂ] E :=
  (TensorProduct.rid ℂ E).toLinearMap ∘ₗ TensorProduct.map LinearMap.id φ

@[simp] lemma tensorContract_tmul (φ : Module.Dual ℂ F) (x : E) (y : F) :
    tensorContract φ (x ⊗ₜ[ℂ] y) = φ y • x := by
  simp [tensorContract]

lemma tensorContract_map (φ : Module.Dual ℂ F) (A : E →ₗ[ℂ] E) (v : E ⊗[ℂ] F) :
    tensorContract φ (TensorProduct.map A LinearMap.id v) = A (tensorContract φ v) := by
  induction v using TensorProduct.inductionOn with
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

def tensorQuotientHom (ρ : Representation ℂ G E) (τ : Representation ℂ G L)
    (Q : L →ₗ[ℂ] E ⊗[ℂ] F)
    (hQ : ∀ g x, Q (τ g x) = TensorProduct.map (ρ g) LinearMap.id (Q x)) :
    Module.Dual ℂ F →ₗ[ℂ] Representation.IntertwiningMap τ ρ where
  toFun φ := (tensorContract φ ∘ₗ Q).intertwiningMap_of_isIntertwiningMap τ ρ (by
    intro g x
    change tensorContract φ (Q (τ g x)) = ρ g (tensorContract φ (Q x))
    rw [hQ, tensorContract_map])
  map_add' φ ψ := by
    apply Representation.IntertwiningMap.ext
    ext x
    change tensorContract (φ + ψ) (Q x) = tensorContract φ (Q x) + tensorContract ψ (Q x)
    have he (v : E ⊗[ℂ] F) : tensorContract (φ+ψ) v = tensorContract φ v + tensorContract ψ v := by
      induction v using TensorProduct.inductionOn with
      | tmul x y => simp [add_smul]
      | add x y hx hy => simp only [map_add, hx, hy]; abel
    exact he _
  map_smul' c φ := by
    apply Representation.IntertwiningMap.ext
    ext x
    change tensorContract (c • φ) (Q x) = c • tensorContract φ (Q x)
    have he (v : E ⊗[ℂ] F) : tensorContract (c • φ) v = c • tensorContract φ v := by
      induction v using TensorProduct.inductionOn with
      | tmul x y => simp [smul_smul]
      | add x y hx hy => simp only [map_add, hx, hy, smul_add]
    exact he _

lemma tensorQuotientHom_injective [Nontrivial E]
    (ρ : Representation ℂ G E) (τ : Representation ℂ G L)
    (Q : L →ₗ[ℂ] E ⊗[ℂ] F)
    (hQ : ∀ g x, Q (τ g x) = TensorProduct.map (ρ g) LinearMap.id (Q x))
    (hQs : Function.Surjective Q) : Function.Injective (tensorQuotientHom ρ τ Q hQ) := by
  intro φ ψ hφψ
  ext y
  obtain ⟨x,hx⟩ := exists_ne (0 : E)
  obtain ⟨v,hv⟩ := hQs (x ⊗ₜ[ℂ] y)
  have he := congrArg (fun f : Representation.IntertwiningMap τ ρ => f v) hφψ
  change tensorContract φ (Q v) = tensorContract ψ (Q v) at he
  rw [hv, tensorContract_tmul, tensorContract_tmul] at he
  exact (smul_left_injective ℂ hx) he

theorem tensor_quotient_multiplicity [Nontrivial E] [FiniteDimensional ℂ E]
    [FiniteDimensional ℂ F] [FiniteDimensional ℂ L]
    (ρ : Representation ℂ G E) (τ : Representation ℂ G L)
    (Q : L →ₗ[ℂ] E ⊗[ℂ] F)
    (hQ : ∀ g x, Q (τ g x) = TensorProduct.map (ρ g) LinearMap.id (Q x))
    (hQs : Function.Surjective Q) :
    finrank ℂ F ≤ finrank ℂ (Representation.IntertwiningMap τ ρ) := by
  simpa only [Subspace.dual_finrank_eq] using
    LinearMap.finrank_le_finrank_of_injective (tensorQuotientHom_injective ρ τ Q hQ hQs)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {E F L G H : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [FiniteDimensional ℂ L]

theorem multiplicity_of_outerTensor_occurrence
    (ρ : Representation ℂ G E) (σ : Representation ℂ H F)
    (τ : Representation ℂ (G × H) L)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (hσ : ∀ g x, ‖σ g x‖ = ‖x‖)
    (hτ : ∀ g x, ‖τ g x‖ = ‖x‖) [ρ.IsIrreducible] [σ.IsIrreducible]
    [Nontrivial E] [Nontrivial F]
    (f : Representation.IntertwiningMap (outerTensorRepresentation ρ σ) τ) (hf : f ≠ 0) :
    finrank ℂ F ≤
      finrank ℂ (Representation.IntertwiningMap (τ.comp (MonoidHom.inl G H)) ρ) := by
  let := outerTensorRepresentation_irreducible ρ σ hρ hσ
  obtain ⟨j,hj⟩ := intertwiner_isometric_normalization _ τ
    (outerTensorRepresentation_norm ρ σ hρ hσ) hτ f hf
  let Q := adjointIntertwiner (outerTensorRepresentation ρ σ) τ
    (outerTensorRepresentation_norm ρ σ hρ hσ) hτ j
  apply tensor_quotient_multiplicity ρ (τ.comp (MonoidHom.inl G H)) Q.toLinearMap
  · intro g x
    have he := Representation.IntertwiningMap.isIntertwining τ (outerTensorRepresentation ρ σ) Q (g,1) x
    change Q (τ (g,1) x) = TensorProduct.map (ρ g) LinearMap.id (Q x)
    rw [show TensorProduct.map (ρ g) LinearMap.id = outerTensorRepresentation ρ σ (g,1) by
      simp only [outerTensorRepresentation_apply, map_one, Module.End.one_eq_id]]
    exact he
  · intro x
    exact ⟨j x, adjoint_isometric_intertwiner _ _ j hj x⟩

end SignedSweeps
end

end OAI
