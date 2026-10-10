import OAI.Analysis.KadisonKastler.UniformProjectionGap
import OAI.Analysis.KadisonKastler.ProjectionCentralSpace

namespace OAI

/-! # Projection centrality forces scalar vectors -/

namespace KadisonKastler

open Generator.Tracial NormedSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance projectionScalarRealInner : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

omit [CompleteSpace H] in
theorem conjugation_stable_submodule_scalar
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (ξ : H) (hξ : J ξ=ξ) (huξ : ‖ξ‖=1) (V : Submodule ℂ H) (hξV : ξ∈V)
    (hJV : ∀ x∈V, J x∈V)
    (hzero : ∀ x∈V, J x=x → inner ℂ ξ x=0 → x=0) :
    ∀ η∈V, ∃ z : ℂ, η=z • ξ := by
  intro η hη
  let z := inner ℂ ξ η
  let v := η-z • ξ
  have hv : v∈V := V.sub_mem hη (V.smul_mem z hξV)
  have horth : inner ℂ ξ v=0 := by
    simp [v,z,inner_self_eq_norm_sq_to_K,huξ]
  have hjorth : inner ℂ ξ (J v)=0 := by
    have he := conjugateIsometry_inner J ξ v
    rw [hξ,horth,star_zero] at he
    exact he
  have hr : v+J v=0 := hzero _ (V.add_mem hv (hJV v hv))
    (by rw [map_add,hJ,add_comm]) (by rw [inner_add_right,horth,hjorth,add_zero])
  have hi : Complex.I • (v-J v)=0 := hzero _ (V.smul_mem _ (V.sub_mem hv (hJV v hv)))
    (by
      rw [J.map_smulₛₗ,map_sub,hJ]
      simp only [Complex.conj_I]
      module)
    (by rw [inner_smul_right,inner_sub_right,horth,hjorth,sub_self,mul_zero])
  have hs : v-J v=0 := (smul_eq_zero.mp hi).resolve_left Complex.I_ne_zero
  have hv0 : v=0 := by
    have hvj := sub_eq_zero.mp hs
    rw [← hvj] at hr
    have hs2 : (2:ℂ) • v=0 := by simpa only [two_smul] using hr
    exact (smul_eq_zero.mp hs2).resolve_left (by norm_num)
  refine ⟨z,?_⟩
  exact sub_eq_zero.mp hv0

variable [TopologicalSpace.SeparableSpace H]

theorem projectionCentral_symmetric_orthogonal_eq_zero
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (huξ : ‖ξ‖=1)
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (hIII : TypeIIIFactor M) (hremote : UniversalModularCoisometries M J)
    (η : H) (hc : η∈projectionCentralSpace (M := M) J ξ)
    (hη : J η=η) (horth : inner ℂ ξ η=0) : η=0 := by
  by_contra hne
  let v := normalize η
  have hv : v∈projectionCentralSpace (M := M) J ξ := by
    change ((‖η‖⁻¹ : ℝ) : ℂ) • η ∈ projectionCentralSpace (M := M) J ξ
    exact (projectionCentralSpace J ξ).smul_mem _ hc
  have hjv : J v=v := by
    change J (((‖η‖⁻¹ : ℝ) : ℂ) • η)=((‖η‖⁻¹ : ℝ) : ℂ) • η
    rw [J.map_smulₛₗ,Complex.conj_ofReal,hη]
  have hov : inner ℂ ξ v=0 := by
    change inner ℂ ξ (((‖η‖⁻¹ : ℝ) : ℂ) • η)=0
    rw [inner_smul_right,horth,mul_zero]
  obtain ⟨δ,hδ,hd⟩ := hv (1/4096) (by norm_num)
  obtain ⟨p,hpξ,hpη⟩ := exists_uniform_projection_gap J hJ hright hleft ξ hξ huξ hsep hpos
    hIII hremote v hjv (norm_normalize hne) hov (δ^2) (sq_pos_of_pos hδ)
  have hp : ‖projectionVectorDefect J p ξ‖<δ := by
    rw [projectionVectorDefect_eq]
    nlinarith [norm_nonneg (centralVectorDefect J ξ p.val.val)]
  have hvp := hd p hp
  rw [projectionVectorDefect_eq] at hvp
  nlinarith [norm_nonneg (centralVectorDefect J v p.val.val)]

theorem projectionCentralSpace_scalar
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (huξ : ‖ξ‖=1)
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (hIII : TypeIIIFactor M) (hremote : UniversalModularCoisometries M J)
    (η : H) (hη : η∈projectionCentralSpace (M := M) J ξ) :
    ∃ z : ℂ, η=z • ξ :=
  conjugation_stable_submodule_scalar J hJ ξ hξ huξ (projectionCentralSpace J ξ)
    (reference_mem_projectionCentralSpace J ξ)
    (fun _ hx => conjugate_mem_projectionCentralSpace J hJ ξ hx)
    (fun x hx hj ho => projectionCentral_symmetric_orthogonal_eq_zero J hJ hright hleft
      ξ hξ huξ hsep hpos hIII hremote x hx hj ho) η hη

end

end KadisonKastler

end OAI
