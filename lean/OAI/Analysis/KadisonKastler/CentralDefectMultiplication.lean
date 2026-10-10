import OAI.Analysis.KadisonKastler.CentralDefectSelfAdjoint

namespace OAI

/-! # Product estimates for the central-vector defect -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem centralVectorDefect_mul
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (a b : Algebra M) :
    centralVectorDefect J ξ (a*b).val =
      a.val (centralVectorDefect J ξ b.val) +
        conjugationOperator J (star b).val (centralVectorDefect J ξ a.val) := by
  have hc := VonNeumannAlgebra.mem_commutant_iff.mp (hright (star b)) a.val a.property
  have he : a.val (conjugationOperator J (star b).val ξ) =
      conjugationOperator J (star b).val (a.val ξ) :=
    congrArg (fun T : H →L[ℂ] H => T ξ) hc
  simp only [StarMemClass.coe_star] at he
  simp only [centralVectorDefect_apply,MulMemClass.coe_mul,star_mul,
    conjugationOperator_mul J hJ,mul_apply_eq_comp,map_sub,StarMemClass.coe_star]
  rw [he]
  abel

theorem centralVectorDefect_mul_norm_le
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (a b : Algebra M) :
    ‖centralVectorDefect J ξ (a*b).val‖ ≤
      ‖a‖ * ‖centralVectorDefect J ξ b.val‖ +
        ‖b‖ * ‖centralVectorDefect J ξ a.val‖ := by
  rw [centralVectorDefect_mul J hJ hright]
  apply (norm_add_le _ _).trans
  apply add_le_add (a.val.le_opNorm _)
  have hn := (conjugationOperator J (star b).val).le_opNorm (centralVectorDefect J ξ a.val)
  rwa [norm_conjugationOperator J hJ,StarMemClass.coe_star,norm_star] at hn

theorem centralVectorDefect_norm_le
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) (ξ : H) (a : H →L[ℂ] H) :
    ‖centralVectorDefect J ξ a‖ ≤ 2 * ‖ξ‖ * ‖a‖ := by
  rw [centralVectorDefect_apply]
  calc
    _ ≤ ‖a ξ‖ + ‖conjugationOperator J (star a) ξ‖ := norm_sub_le _ _
    _ ≤ ‖a‖ * ‖ξ‖ + ‖conjugationOperator J (star a)‖ * ‖ξ‖ :=
      add_le_add (a.le_opNorm ξ) ((conjugationOperator J (star a)).le_opNorm ξ)
    _ = _ := by rw [norm_conjugationOperator J hJ,norm_star]; ring

theorem centralVectorDefect_one (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) (ξ : H) :
    centralVectorDefect J ξ (1 : H →L[ℂ] H) = 0 := by
  rw [centralVectorDefect_apply,star_one,conjugationOperator_one J hJ,sub_self]

end

end KadisonKastler

end OAI
