import OAI.Analysis.KadisonKastler.UnitaryStateDefect

namespace OAI

/-! # Centered cyclic approximation and commutator defects -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem exists_centered_algebra_vector_near_of_mem_closure
    (ξ : H) (hunit : ‖ξ‖=1) (η : H) (horth : inner ℂ ξ η=0)
    (hηclosure : η ∈ closure (Set.range (algebraVectorMap M ξ)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ a : Algebra M, vectorFunctional (M := M) ξ a=0 ∧ ‖a.val ξ-η‖ < ε := by
  obtain ⟨v,⟨a,rfl⟩,ha⟩ := Metric.mem_closure_iff.mp hηclosure (ε/2) (half_pos hε)
  have hd : ‖a.val ξ-η‖ < ε/2 := by
    change dist η (a.val ξ) < ε/2 at ha
    simpa only [dist_eq_norm,norm_sub_rev] using ha
  let c : ℂ := inner ℂ ξ (a.val ξ)
  let b : Algebra M := a-c • 1
  have hbe : b.val ξ=a.val ξ-c • ξ := by
    change (a.val-c • (1 : H →L[ℂ] H)) ξ=_
    simp only [sub_apply,smul_apply,one_apply_eq_self]
  have hself : inner ℂ ξ ξ=1 := by
    rw [inner_self_eq_norm_sq_to_K,hunit]
    norm_num
  have hc : ‖c‖ ≤ ‖a.val ξ-η‖ := by
    have he : c=inner ℂ ξ (a.val ξ-η) := by rw [inner_sub_right,horth,sub_zero]
    rw [he]
    simpa only [hunit,one_mul] using norm_inner_le_norm ξ (a.val ξ-η)
  refine ⟨b,?_,?_⟩
  · change inner ℂ ξ (b.val ξ)=0
    rw [hbe,inner_sub_right,inner_smul_right,hself,mul_one]
    exact sub_self c
  · rw [hbe]
    have he : a.val ξ-c • ξ-η=(a.val ξ-η)-c • ξ := by abel
    rw [he]
    have hn := norm_sub_le (a.val ξ-η) (c • ξ)
    rw [norm_smul,hunit,mul_one] at hn
    linarith

theorem exists_centered_algebra_vector_near
    (ξ : H) (hunit : ‖ξ‖=1) (hcyc : DenseRange (algebraVectorMap M ξ))
    (η : H) (horth : inner ℂ ξ η=0) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : Algebra M, vectorFunctional (M := M) ξ a=0 ∧ ‖a.val ξ-η‖ < ε :=
  exists_centered_algebra_vector_near_of_mem_closure ξ hunit η horth (hcyc η) ε hε

theorem centralVectorDefect_on_algebra_vector
    (J : H ≃ₗᵢ⋆[ℂ] H)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (a b : Algebra M) :
    centralVectorDefect J (a.val ξ) b.val =
      (b*a-a*b).val ξ+a.val (centralVectorDefect J ξ b.val) := by
  have hc := VonNeumannAlgebra.mem_commutant_iff.mp (hright (star b)) a.val a.property
  have he := congrArg (fun T : H →L[ℂ] H => T ξ) hc
  change a.val (conjugationOperator J (star b).val ξ)=
    conjugationOperator J (star b).val (a.val ξ) at he
  change a.val (conjugationOperator J (star b.val) ξ)=
    conjugationOperator J (star b.val) (a.val ξ) at he
  change b.val (a.val ξ)-conjugationOperator J (star b.val) (a.val ξ)=
    (b.val (a.val ξ)-a.val (b.val ξ))+
      a.val (b.val ξ-conjugationOperator J (star b.val) ξ)
  rw [map_sub,← he]
  abel

theorem commutator_vector_norm_le_central_defects
    (J : H ≃ₗᵢ⋆[ℂ] H)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (a b : Algebra M) :
    ‖(b*a-a*b).val ξ‖ ≤ ‖centralVectorDefect J (a.val ξ) b.val‖+
      ‖a‖*‖centralVectorDefect J ξ b.val‖ := by
  have he := centralVectorDefect_on_algebra_vector J hright ξ a b
  have h : (b*a-a*b).val ξ=centralVectorDefect J (a.val ξ) b.val-
      a.val (centralVectorDefect J ξ b.val) := by rw [he]; abel
  rw [h]
  exact (norm_sub_le _ _).trans (add_le_add le_rfl (a.val.le_opNorm _))

theorem centralVectorDefect_vector_lipschitz
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (ξ η : H) (a : H →L[ℂ] H) :
    ‖centralVectorDefect J ξ a‖ ≤ ‖centralVectorDefect J η a‖+2*‖ξ-η‖*‖a‖ := by
  have he : centralVectorDefect J ξ a=centralVectorDefect J η a+
      centralVectorDefect J (ξ-η) a := by
    simp only [centralVectorDefect_apply,map_sub]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add le_rfl
    (centralVectorDefect_norm_le J hJ (ξ-η) a))

end

end KadisonKastler

end OAI
