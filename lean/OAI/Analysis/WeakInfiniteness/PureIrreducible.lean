import Mathlib
import OAI.Analysis.WeakInfiniteness.InvariantSubspaces

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma RepresentationInvariant.eq_bot_of_projected_cyclic_zero
    {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {S : Submodule ℂ H} [S.HasOrthogonalProjection]
    (hS : RepresentationInvariant π S) (Ω : H)
    (hd : DenseRange (fun a : A => π a Ω)) (hΩ : S.starProjection Ω=0) : S=⊥ := by
  have hzero : ∀ x : H,S.starProjection x=0 := isClosed_property hd
    (isClosed_eq S.starProjection.continuous continuous_const) (by
      intro a
      rw [hS.projection_commutes,hΩ,map_zero])
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_bot]
    rw [← S.starProjection_eq_self_iff.mpr hx]
    exact hzero x
  · exact bot_le

variable [PartialOrder A] [StarOrderedRing A]

theorem irreducible_of_extreme_cyclic_vector_state
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H) (hΩ : ‖Ω‖=1)
    (hd : DenseRange (fun a : A => π a Ω))
    (hf : StrongDual.toWeakDual (representationVectorFunctional π Ω) ∈
      (realStateSpace A).extremePoints ℝ) : RepresentationIrreducible π := by
  intro S hSc hS
  let : CompleteSpace S := hSc.isComplete.completeSpace_coe
  by_cases h0 : S.starProjection Ω=0
  · exact Or.inl (hS.eq_bot_of_projected_cyclic_zero Ω hd h0)
  by_cases h1 : Sᗮ.starProjection Ω=0
  · right
    have he : Sᗮ=⊥ := hS.orthogonal.eq_bot_of_projected_cyclic_zero Ω hd h1
    have he' := congrArg Submodule.orthogonal he
    simpa using he'
  exfalso
  let t : ℝ := ‖S.starProjection Ω‖^2
  let s : ℝ := ‖Sᗮ.starProjection Ω‖^2
  have ht : 0 < t := sq_pos_of_pos (norm_pos_iff.mpr h0)
  have hs : 0 < s := sq_pos_of_pos (norm_pos_iff.mpr h1)
  have hts : t+s=1 := by
    have h := Submodule.norm_sq_eq_add_norm_sq_starProjection Ω S
    rw [hΩ,one_pow] at h
    exact h.symm
  let g := StrongDual.toWeakDual (t⁻¹ • representationVectorFunctional π (S.starProjection Ω))
  let k := StrongDual.toWeakDual (s⁻¹ • representationVectorFunctional π (Sᗮ.starProjection Ω))
  have hg : g ∈ realStateSpace A := normalized_vector_mem_realStateSpace π h0
  have hk : k ∈ realStateSpace A := normalized_vector_mem_realStateSpace π h1
  have hsum : t • g+s • k=StrongDual.toWeakDual (representationVectorFunctional π Ω) := by
    apply DFunLike.ext
    intro b
    change t*(t⁻¹*representationVectorFunctional π (S.starProjection Ω) b)+
      s*(s⁻¹*representationVectorFunctional π (Sᗮ.starProjection Ω) b)=
        representationVectorFunctional π Ω b
    rw [← mul_assoc t, mul_inv_cancel₀ ht.ne',one_mul,
      ← mul_assoc s,mul_inv_cancel₀ hs.ne',one_mul]
    exact (DFunLike.congr_fun (hS.vectorFunctional_decomposition Ω) b).symm
  have hgf : g=StrongDual.toWeakDual (representationVectorFunctional π Ω) :=
    hf.2 hg hk ⟨t,s,ht,hs,hts,hsum⟩
  have hnorm : ∀ x : H,‖S.starProjection x‖^2=t*‖x‖^2 := by
    apply isClosed_property hd (isClosed_eq (by fun_prop) (by fun_prop))
    intro a
    have he := DFunLike.congr_fun hgf
      ⟨star a*a,(star_mul_self_nonneg a).isSelfAdjoint⟩
    change t⁻¹*representationVectorFunctional π (S.starProjection Ω)
      ⟨star a*a,(star_mul_self_nonneg a).isSelfAdjoint⟩=
        representationVectorFunctional π Ω ⟨star a*a,(star_mul_self_nonneg a).isSelfAdjoint⟩ at he
    rw [representationVectorFunctional_square,representationVectorFunctional_square] at he
    rw [hS.projection_commutes]
    have hem := congrArg (fun r : ℝ => t*r) he
    rw [← mul_assoc,mul_inv_cancel₀ ht.ne',one_mul] at hem
    exact hem
  have he := hnorm (S.starProjection Ω)
  rw [S.starProjection_eq_self_iff.mpr (S.starProjection_apply_mem Ω)] at he
  change t=t*t at he
  nlinarith

theorem extreme_real_state_gns_irreducible
    (f : WeakDual ℝ (selfAdjoint A)) (hf : f ∈ (realStateSpace A).extremePoints ℝ) :
    RepresentationIrreducible (realStateComplexification f hf.1).gnsStarAlgHom := by
  let Φ := realStateComplexification f hf.1
  apply irreducible_of_extreme_cyclic_vector_state Φ.gnsStarAlgHom (gnsCyclicVector Φ)
  · exact norm_gnsCyclicVector Φ (realStateComplexification_one f hf.1)
  · exact gnsAction_cyclic_dense Φ
  · rwa [gns_vectorFunctional_eq]

end

end WeakPureInfiniteness
end

end OAI
