import OAI.Analysis.KadisonKastler.ProjectionVectorDomination
import OAI.Analysis.KadisonKastler.PartialIsometryVectorEnergy
import OAI.Analysis.KadisonKastler.TypeIIIProjectionComparison

namespace OAI

/-! # Two-vector witnesses when the test state is not dominated

A small positive cut of a projection of large relative state weight is
equivalent to its complement in the type III factor. The resulting partial
isometry has large test displacement and small reference displacement.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

theorem exists_nondominated_two_vector_witness (hM : TypeIIIFactor M)
    (J : H ≃ₗᵢ⋆[ℂ] H) (ξ η : H) (hξ : J ξ=ξ) (hη : J η=η)
    (hnot : ¬ ∃ C : ℝ, ∀ a : Algebra M, ‖a.val η‖ ≤ C*‖a.val ξ‖)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ a : Algebra M, ‖a.val ξ‖+‖a.val η‖ < 12*‖centralVectorDefect J η a.val‖ ∧
      ‖centralVectorDefect J ξ a.val‖ < γ*‖centralVectorDefect J η a.val‖ := by
  let R := 16/γ^2+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hR₁ : 1 ≤ R := by
    dsimp [R]
    have he : 0 ≤ 16/γ^2 := by positivity
    linarith
  obtain ⟨p,hp⟩ := exists_projection_large_vector_ratio ξ η hnot R hR.le
  have hpη : 0 < ‖p.val.val η‖^2 := lt_of_le_of_lt
    (mul_nonneg hR.le (sq_nonneg _)) hp
  obtain ⟨q,hqp,hqη,hqsmall⟩ := hM.exists_small_positive_vector_subprojection p η hpη
    (show 0 < ‖p.val.val η‖^2/16 by positivity)
  let r : AlgebraProjection M := ⟨p.val-q.val,q.property.sub_of_mul_eq_right p.property hqp⟩
  have hweights (ζ : H) : ‖q.val.val ζ‖^2+‖r.val.val ζ‖^2=‖p.val.val ζ‖^2 :=
    vector_projection_sub_weight p q hqp ζ
  have hq0 : q.val ≠ 0 := by
    intro hz
    have hzv : q.val.val=0 := congrArg Subtype.val hz
    have he : (0 : ℝ) < 0 := by
      simpa only [hzv,zero_apply,norm_zero,pow_two,mul_zero] using hqη
    exact (lt_irrefl 0) he
  have hr0 : r.val ≠ 0 := by
    intro hz
    have hzv : r.val.val=0 := congrArg Subtype.val hz
    have hh := hweights η
    simp only [hzv,zero_apply,norm_zero,pow_two,mul_zero,add_zero] at hh
    nlinarith only [hpη,hqsmall,hh]
  have hr1 : r.Equivalent (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M) :=
    projection_equivalent_one_of_not_finite hM.factor r
      (fun hf => hr0 (hM.purelyInfinite r.val r.property hf))
  have hq1 : q.Equivalent (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M) :=
    projection_equivalent_one_of_not_finite hM.factor q
      (fun hf => hq0 (hM.purelyInfinite q.val q.property hf))
  obtain ⟨v,hvs,hvt⟩ := AlgebraProjection.equivalent_trans hr1
    (AlgebraProjection.equivalent_symm hq1)
  have hvnorm (ζ : H) : ‖v.val.val ζ‖^2=‖r.val.val ζ‖^2 := by
    rw [partialIsometry_vector_norm_sq,hvs]
  have hgap : ‖p.val.val η‖^2/4 < ‖centralVectorDefect J η v.val.val‖^2 :=
    partialIsometry_central_defect_lower J v p q (congrArg Subtype.val hvs) hvt hqp η hη hqsmall
  have hcent : ‖centralVectorDefect J ξ v.val.val‖^2 ≤ 2*‖p.val.val ξ‖^2 := by
    have he := partialIsometry_central_defect_upper J v ξ hξ
    rw [hvs,hvt] at he
    have hw := hweights ξ
    nlinarith only [he,hw]
  have hpξ : ‖p.val.val ξ‖^2 < ‖p.val.val η‖^2 := by
    exact (le_mul_of_one_le_left (sq_nonneg _) hR₁).trans_lt hp
  have hsum : (‖v.val.val ξ‖+‖v.val.val η‖)^2 <
      16*‖centralVectorDefect J η v.val.val‖^2 := by
    have hξw := hweights ξ
    have hηw := hweights η
    have hvξ := hvnorm ξ
    have hvη := hvnorm η
    nlinarith only [hξw,hηw,hvξ,hvη,hpξ,hgap,
      sq_nonneg (‖v.val.val ξ‖-‖v.val.val η‖),sq_nonneg ‖q.val.val ξ‖,
      sq_nonneg ‖q.val.val η‖]
  have hD : 0 < ‖centralVectorDefect J η v.val.val‖ := by
    nlinarith only [hgap,hpη,norm_nonneg (centralVectorDefect J η v.val.val)]
  have hsum' : ‖v.val.val ξ‖+‖v.val.val η‖ <
      4*‖centralVectorDefect J η v.val.val‖ := by
    apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
    nlinarith only [hsum]
  have hRval : γ^2*R=16+γ^2 := by
    dsimp [R]
    field_simp
  have hratio : 16*‖p.val.val ξ‖^2 < γ^2*‖p.val.val η‖^2 := by
    have he := mul_lt_mul_of_pos_left hp (sq_pos_of_pos hγ)
    rw [← mul_assoc,hRval] at he
    nlinarith only [he,mul_nonneg (sq_nonneg γ) (sq_nonneg ‖p.val.val ξ‖)]
  have hgapγ := mul_lt_mul_of_pos_left hgap (sq_pos_of_pos hγ)
  refine ⟨v.val,by linarith,?_⟩
  apply (sq_lt_sq₀ (norm_nonneg _) (mul_nonneg hγ.le hD.le)).mp
  rw [mul_pow]
  nlinarith only [hcent,hratio,hgapγ]

end

end KadisonKastler

end OAI
