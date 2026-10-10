import OAI.Analysis.KadisonKastler.TomitaClosedOperator

namespace OAI

/-! # The commutant core lies in the adjoint Tomita domain

The closed-graph coefficient identity identifies the adjoint on the dense
commutant orbit. In particular the adjoint operator is densely defined.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

private theorem tomitaAdjoint_coefficient (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω)) (b : Algebra M.commutant)
    (ξ : (tomitaClosedLinearOperator M J Ω 1).domain) :
    inner ℂ (star b.val Ω) ξ.val =
      inner ℂ (J (b.val Ω)) (tomitaClosedLinearOperator M J Ω 1 ξ) := by
  have hg := LinearPMap.mem_graph (tomitaClosedLinearOperator M J Ω 1) ξ
  rw [tomitaClosedLinearOperator_graph J Ω 1 hsep] at hg
  have hc := rescaledGraph_commutant_coefficient J Ω 1 b
    (tomitaProductCoordinates.symm (ξ.val, tomitaClosedLinearOperator M J Ω 1 ξ)) hg
  change inner ℂ (J (b.val Ω)) (tomitaClosedLinearOperator M J Ω 1 ξ) =
    (1 : ℂ) * inner ℂ (star b.val Ω) ξ.val at hc
  simpa only [one_mul] using hc.symm

theorem tomitaAdjoint_commutant_mem (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω)) (b : Algebra M.commutant) :
    J (b.val Ω) ∈ (tomitaClosedLinearOperator M J Ω 1).adjoint.domain :=
  LinearPMap.mem_adjoint_domain_of_exists _
    ⟨star b.val Ω, tomitaAdjoint_coefficient J Ω hsep b⟩

theorem tomitaAdjoint_commutant_apply (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (b : Algebra M.commutant) :
    (tomitaClosedLinearOperator M J Ω 1).adjoint
      ⟨J (b.val Ω), tomitaAdjoint_commutant_mem J Ω hsep b⟩ = star b.val Ω :=
  LinearPMap.adjoint_apply_eq (tomitaClosedLinearOperator_dense J Ω 1 hsep hcyc) _
    (tomitaAdjoint_coefficient J Ω hsep b)

/-- Separation makes the commutant orbit dense, hence the adjoint domain dense. -/
theorem tomitaAdjoint_dense (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω)) :
    Dense ((tomitaClosedLinearOperator M J Ω 1).adjoint.domain : Set H) := by
  have hd := Generator.commutant_orbit_dense M Ω (fun a ha => by
    apply hsep
    exact ha)
  intro x
  let D : Set H := (tomitaClosedLinearOperator M J Ω 1).adjoint.domain
  have hc : IsClosed {v : H | J v ∈ closure D} := isClosed_closure.preimage J.continuous
  have hsub : Set.range (fun b : Algebra M.commutant => b.val Ω) ⊆
      {v : H | J v ∈ closure D} := by
    rintro _ ⟨b, rfl⟩
    exact subset_closure (tomitaAdjoint_commutant_mem J Ω hsep b)
  have h := closure_minimal hsub hc (hd (J.symm x))
  change J (J.symm x) ∈ closure D at h
  simpa only [J.apply_symm_apply] using h

end

end KadisonKastler

end OAI
