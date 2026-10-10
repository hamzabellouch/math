import OAI.Analysis.KadisonKastler.HaagerupBoundedVectorWitness
import OAI.Analysis.KadisonKastler.SelfAdjointCentralGap

namespace OAI

/-! # Self-adjoint two-vector witnesses

The real and imaginary parts are controlled on the two specified vectors,
rather than in operator norm. This is the reduction used before the
spectral cuts in Haagerup's Lemma 2.10.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem adjoint_vector_norm_le_defect (J : H ≃ₗᵢ⋆[ℂ] H)
    (ξ : H) (hξ : J ξ=ξ) (a : H →L[ℂ] H) :
    ‖star a ξ‖ ≤ ‖a ξ‖+‖centralVectorDefect J ξ a‖ := by
  have he : ‖star a ξ‖=‖conjugationOperator J (star a) ξ‖ := by
    simp only [conjugationOperator_apply,hξ,J.norm_map]
  rw [he]
  calc
    _ ≤ ‖a ξ‖+‖a ξ-conjugationOperator J (star a) ξ‖ := by
      simpa only [norm_sub_rev] using
        (norm_le_norm_add_norm_sub' (conjugationOperator J (star a) ξ) (a ξ))
    _ = _ := rfl

theorem realPart_vector_norm_le (J : H ≃ₗᵢ⋆[ℂ] H)
    (ξ : H) (hξ : J ξ=ξ) (a : H →L[ℂ] H) :
    ‖(realPart a : H →L[ℂ] H) ξ‖ ≤
      ‖a ξ‖+‖centralVectorDefect J ξ a‖/2 := by
  rw [realPart_apply_coe,smul_apply,add_apply,norm_smul]
  rw [show ‖(2 : ℝ)⁻¹‖=(1/2 : ℝ) by norm_num]
  have hs := adjoint_vector_norm_le_defect J ξ hξ a
  have hn := norm_add_le (a ξ) (star a ξ)
  nlinarith

theorem imaginaryPart_vector_norm_le (J : H ≃ₗᵢ⋆[ℂ] H)
    (ξ : H) (hξ : J ξ=ξ) (a : H →L[ℂ] H) :
    ‖(imaginaryPart a : H →L[ℂ] H) ξ‖ ≤
      ‖a ξ‖+‖centralVectorDefect J ξ a‖/2 := by
  rw [imaginaryPart_apply_coe,smul_apply,smul_apply,sub_apply,norm_smul,norm_smul]
  rw [norm_neg,Complex.norm_I,one_mul,
    show ‖(2 : ℝ)⁻¹‖=(1/2 : ℝ) by norm_num]
  have hs := adjoint_vector_norm_le_defect J ξ hξ a
  have hn := norm_sub_le (a ξ) (star a ξ)
  nlinarith

theorem exists_selfAdjoint_two_vector_gap
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (ξ η : H) (hξ : J ξ=ξ) (hη : J η=η) (a : Algebra M) :
    ∃ b : Algebra M, IsSelfAdjoint b ∧
      ‖b.val ξ‖+‖b.val η‖ ≤ ‖a.val ξ‖+‖a.val η‖+
        (‖centralVectorDefect J ξ a.val‖+‖centralVectorDefect J η a.val‖)/2 ∧
      ‖centralVectorDefect J ξ b.val‖ ≤ ‖centralVectorDefect J ξ a.val‖ ∧
      ‖centralVectorDefect J η a.val‖/2 ≤ ‖centralVectorDefect J η b.val‖ := by
  rcases centralVectorDefect_re_im_gap J η a.val with hr | hi
  · let b : Algebra M := ⟨(realPart a.val : H →L[ℂ] H),realPart_mem_vonNeumann M a.property⟩
    refine ⟨b,Subtype.ext (realPart a.val).property.star_eq,?_,
      centralVectorDefect_realPart_le J hJ ξ hξ a.val,hr⟩
    change ‖(realPart a.val : H →L[ℂ] H) ξ‖+
      ‖(realPart a.val : H →L[ℂ] H) η‖ ≤ _
    linarith [realPart_vector_norm_le J ξ hξ a.val,realPart_vector_norm_le J η hη a.val]
  · have hb : (imaginaryPart a.val : H →L[ℂ] H) ∈ M := by
      rw [imaginaryPart_apply_coe,← Complex.coe_smul (2 : ℝ)⁻¹]
      exact M.smul_mem (M.smul_mem (M.sub_mem a.property (M.star_mem' a.property)) _) _
    let b : Algebra M := ⟨(imaginaryPart a.val : H →L[ℂ] H),hb⟩
    refine ⟨b,Subtype.ext (imaginaryPart a.val).property.star_eq,?_,
      centralVectorDefect_imaginaryPart_le J hJ ξ hξ a.val,hi⟩
    change ‖(imaginaryPart a.val : H →L[ℂ] H) ξ‖+
      ‖(imaginaryPart a.val : H →L[ℂ] H) η‖ ≤ _
    linarith [imaginaryPart_vector_norm_le J ξ hξ a.val,
      imaginaryPart_vector_norm_le J η hη a.val]

theorem exists_selfAdjoint_relative_two_vector
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (ξ η : H) (hξ : J ξ=ξ) (hη : J η=η)
    (hw : ∀ ε : ℝ, 0 < ε → ∃ a : Algebra M,
      ‖a.val ξ‖+‖a.val η‖ < 12*‖centralVectorDefect J η a.val‖ ∧
      ‖centralVectorDefect J ξ a.val‖ < ε*‖centralVectorDefect J η a.val‖)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ b : Algebra M, IsSelfAdjoint b ∧
      ‖b.val ξ‖+‖b.val η‖ < 26*‖centralVectorDefect J η b.val‖ ∧
      ‖centralVectorDefect J ξ b.val‖ < δ*‖centralVectorDefect J η b.val‖ := by
  let γ := min (δ/2) 1
  have hγ : 0 < γ := lt_min (by positivity) zero_lt_one
  obtain ⟨a,hsize,hdef⟩ := hw γ hγ
  obtain ⟨b,hb,hsizeb,hdefb,hgapb⟩ :=
    exists_selfAdjoint_two_vector_gap J hJ ξ η hξ hη a
  have hγ₁ : γ ≤ 1 := min_le_right _ _
  have hγδ : γ ≤ δ/2 := min_le_left _ _
  refine ⟨b,hb,?_,?_⟩
  · have hsmall : ‖centralVectorDefect J ξ a.val‖ < ‖centralVectorDefect J η a.val‖ :=
      hdef.trans_le (mul_le_of_le_one_left (norm_nonneg _) hγ₁)
    linarith
  · have he := mul_le_mul_of_nonneg_right hγδ (norm_nonneg (centralVectorDefect J η a.val))
    nlinarith

namespace ModularConjugationData

variable {Ω : H} (d : ModularConjugationData M Ω)

theorem selfAdjoint_symmetric_vector_witness
    (h : HaagerupCommutatorWitnesses d)
    (a : Algebra M) (hbal : a.val Ω=d.rightAction (star a) Ω)
    (hzero : productVectorState Ω a.val=0) (hnorm : ‖a.val Ω‖=1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ b : Algebra M, IsSelfAdjoint b ∧
      ‖b.val Ω‖+‖b.val (a.val Ω)‖ <
        26*‖centralVectorDefect d.conjugation (a.val Ω) b.val‖ ∧
      ‖centralVectorDefect d.conjugation Ω b.val‖ <
        δ*‖centralVectorDefect d.conjugation (a.val Ω) b.val‖ := by
  let γ := min (δ/2) 1
  have hγ : 0 < γ := lt_min (by positivity) zero_lt_one
  obtain ⟨b,hsize,hdef⟩ := d.bounded_symmetric_vector_witness h a hbal hzero hnorm hγ
  have hη : d.conjugation (a.val Ω)=a.val Ω := by
    have he := d.rightAction_conjugation a Ω
    rw [d.fixes_vector] at he
    exact he.symm.trans hbal.symm
  obtain ⟨c,hc,hsizec,hdefc,hgapc⟩ := exists_selfAdjoint_two_vector_gap
    d.conjugation d.involutive Ω (a.val Ω) d.fixes_vector hη b
  have hdef' : ‖centralVectorDefect d.conjugation Ω b.val‖ <
      γ*‖centralVectorDefect d.conjugation (a.val Ω) b.val‖ := hdef
  have hsize' : ‖b.val Ω‖+‖b.val (a.val Ω)‖ <
      12*‖centralVectorDefect d.conjugation (a.val Ω) b.val‖ := hsize
  have hγ₁ : γ ≤ 1 := min_le_right _ _
  have hγδ : γ ≤ δ/2 := min_le_left _ _
  refine ⟨c,hc,?_,?_⟩
  · have hsmall : ‖centralVectorDefect d.conjugation Ω b.val‖ <
        ‖centralVectorDefect d.conjugation (a.val Ω) b.val‖ :=
      hdef'.trans_le (mul_le_of_le_one_left (norm_nonneg _) hγ₁)
    linarith
  · have he := mul_le_mul_of_nonneg_right hγδ
      (norm_nonneg (centralVectorDefect d.conjugation (a.val Ω) b.val))
    nlinarith

end ModularConjugationData

end

end KadisonKastler

end OAI
