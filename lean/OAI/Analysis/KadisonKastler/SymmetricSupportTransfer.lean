import OAI.Analysis.KadisonKastler.SupportVectorTransfer

namespace OAI

/-! # Support isometries for a symmetric vector in a type III factor -/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_symmetric_support_isometries [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H) (hM : TypeIIIFactor M)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hleft : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hright : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ = ξ) (hne : ξ ≠ 0) :
    ∃ (v : Algebra M) (w : Algebra M.commutant),
      star v * v = 1 ∧ star w * w = 1 ∧
      v.val * star v.val = (vectorSupportProjection M ξ).val.val ∧
      w.val * star w.val = (vectorSupportProjection M.commutant ξ).val.val := by
  let p := vectorSupportProjection M ξ
  have hp : p.val ≠ 0 := by
    intro h
    have he := vectorSupportProjection_apply M ξ
    change p.val.val ξ = ξ at he
    rw [h] at he
    exact hne he.symm
  obtain ⟨v,hv,hvp⟩ := hM.exists_isometry_onto_projection p.val p.property hp
  let w : Algebra M.commutant := ⟨conjugationOperator J v.val,hleft v⟩
  have hw : star w * w = 1 := by
    apply Subtype.ext
    change star (conjugationOperator J v.val) * conjugationOperator J v.val = 1
    rw [← conjugationOperator_star J hJ, ← conjugationOperator_mul J hJ]
    have hv' : star v.val * v.val = 1 := congrArg Subtype.val hv
    rw [hv',conjugationOperator_one J hJ]
  refine ⟨v,w,hv,hw,congrArg Subtype.val hvp,?_⟩
  change conjugationOperator J v.val * star (conjugationOperator J v.val) = _
  rw [← conjugationOperator_star J hJ, ← conjugationOperator_mul J hJ]
  have hvp' : v.val * star v.val = p.val.val := congrArg Subtype.val hvp
  rw [hvp']
  exact (vectorSupportProjection_conjugate M J hJ hleft hright ξ hξ).symm

theorem norm_apply_of_operator_isometry (T : H →L[ℂ] H) (hT : star T * T = 1) (ξ : H) :
    ‖T ξ‖ = ‖ξ‖ := by
  have hi : inner ℂ (T ξ) (T ξ) = inner ℂ ξ ξ := by
    rw [← T.adjoint_inner_right]
    change inner ℂ ξ ((star T * T) ξ) = inner ℂ ξ ξ
    rw [hT,one_apply_eq_self]
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),hi]

theorem support_transfer_norm (M : VonNeumannAlgebra H) (ξ : H)
    (v : Algebra M) (w : Algebra M.commutant)
    (hv : star v * v = 1) (hw : star w * w = 1)
    (hvp : v.val * star v.val = (vectorSupportProjection M ξ).val.val)
    (hwq : w.val * star w.val = (vectorSupportProjection M.commutant ξ).val.val) :
    ‖star (v.val * w.val) ξ‖ = ‖ξ‖ := by
  have hv' : star v.val * v.val = 1 := congrArg Subtype.val hv
  have hw' : star w.val * w.val = 1 := congrArg Subtype.val hw
  have hU : star (v.val * w.val) * (v.val * w.val) = 1 := by
    rw [star_mul]
    calc
      star w.val * star v.val * (v.val * w.val) =
          star w.val * (star v.val * v.val) * w.val := by simp only [mul_assoc]
      _ = 1 := by rw [hv',mul_one,hw']
  have hqv : (vectorSupportProjection M.commutant ξ).val.val * star v.val =
      star v.val * (vectorSupportProjection M.commutant ξ).val.val :=
    (VonNeumannAlgebra.mem_commutant_iff.mp
      (vectorSupportProjection M.commutant ξ).val.property
      (star v.val) (M.star_mem' v.property)).symm
  have hfix : (v.val * w.val) (star (v.val * w.val) ξ) = ξ := by
    change ((v.val * w.val) * star (v.val * w.val)) ξ = ξ
    rw [star_mul]
    have he : (v.val * w.val) * (star w.val * star v.val) =
        (v.val * star v.val) * (w.val * star w.val) := by
      calc
        _ = v.val * ((w.val * star w.val) * star v.val) := by simp only [mul_assoc]
        _ = _ := by rw [hwq,hqv]; simp only [mul_assoc]
    rw [he,hvp,hwq,mul_apply_eq_comp,vectorSupportProjection_apply,vectorSupportProjection_apply]
  exact (norm_apply_of_operator_isometry (v.val * w.val) hU _).symm.trans
    (congrArg norm hfix)

end

end KadisonKastler

end OAI
