import OAI.Analysis.KadisonKastler.CentralDefectProjectionCut

namespace OAI

/-! # Projection cuts for unnormalized central vectors

The reference vector may be a finite-matrix central projection of a unit
vector, and the test vector may be any nonzero residual. The fixed gap
therefore scales with the squared norm of the residual.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem exists_scaled_projection_gap_of_central_defect
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ η : H) (hξ : ‖ξ‖ ≤ 1) (hη : η ≠ 0) (hJξ : J ξ = ξ)
    (a : Algebra M) (ha : ‖a‖ ≤ 1) (δ : ℝ) (hδ : 0 < δ)
    (hsmall : ‖centralVectorDefect J ξ a.val‖ < δ / 64)
    (hgap : ‖η‖ / 2 ≤ ‖centralVectorDefect J η a.val‖) :
    ∃ p : AlgebraProjection M,
      ‖(p.val.val - conjugationOperator J p.val.val) ξ‖ ^ 2 ≤ δ ∧
      (1 / 128 : ℝ) * ‖η‖ ^ 2 ≤
        ‖(p.val.val - conjugationOperator J p.val.val) η‖ ^ 2 := by
  have hn : 0 < ‖η‖ := norm_pos_iff.mpr hη
  let η₀ : H := ‖η‖⁻¹ • η
  have hn₀ : ‖η₀‖ = 1 := by
    dsimp only [η₀]
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hn.le),inv_mul_cancel₀ hn.ne']
  have hD : ‖centralVectorDefect J η₀ a.val‖ =
      ‖η‖⁻¹ * ‖centralVectorDefect J η a.val‖ := by
    change ‖(a.val - conjugationOperator J (star a.val)) (‖η‖⁻¹ • η)‖ = _
    rw [ContinuousLinearMap.map_smul_of_tower,norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hn.le)]
    rfl
  have hgap₀ : (1 / 2 : ℝ) ≤ ‖centralVectorDefect J η₀ a.val‖ := by
    rw [hD]
    have ht := mul_le_mul_of_nonneg_left hgap (inv_nonneg.mpr hn.le)
    simpa only [← mul_div_assoc,inv_mul_cancel₀ hn.ne',one_div] using ht
  obtain ⟨b,hbs,hbn,hbsmall,hbgap⟩ := exists_selfAdjoint_central_gap J hJ ξ η₀ hJξ a
  have hbstar : star b.val = b.val := congrArg Subtype.val hbs.star_eq
  have hbe (ζ : H) : centralVectorDefect J ζ b.val =
      (b.val - conjugationOperator J b.val) ζ := by
    rw [centralVectorDefect_apply,hbstar]
    rfl
  rw [hbe] at hbsmall hbgap
  have hbref : ‖(b.val - conjugationOperator J b.val) ξ‖ * ‖ξ‖ < δ / 64 :=
    (mul_le_of_le_one_right (norm_nonneg _) hξ).trans_lt (hbsmall.trans_lt hsmall)
  have hbtest : (1 / 4 : ℝ) ≤ ‖(b.val - conjugationOperator J b.val) η₀‖ := by
    linarith
  have henergy : ‖(b.val - conjugationOperator J b.val) ξ‖ * ‖ξ‖ <
      δ * (‖(b.val - conjugationOperator J b.val) η₀‖ ^ 2 / 2 - 2 * (1/128:ℝ)) := by
    have ht : (1/64:ℝ) ≤ ‖(b.val - conjugationOperator J b.val) η₀‖ ^ 2 / 2 -
        2 * (1/128:ℝ) := by nlinarith
    have hm := mul_le_mul_of_nonneg_left ht hδ.le
    nlinarith
  obtain ⟨p,hpref,hptest⟩ := exists_selfAdjoint_projection_cut J hJ hright b hbs
    (hbn.trans ha) ξ η₀ hn₀ δ (1/128) hδ (by norm_num) henergy
  refine ⟨p,hpref,?_⟩
  have he : ‖(p.val.val - conjugationOperator J p.val.val) η₀‖ =
      ‖η‖⁻¹ * ‖(p.val.val - conjugationOperator J p.val.val) η‖ := by
    dsimp only [η₀]
    rw [ContinuousLinearMap.map_smul_of_tower,norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hn.le)]
  rw [he,mul_pow] at hptest
  have hm := mul_le_mul_of_nonneg_right hptest (sq_nonneg ‖η‖)
  have hi : ‖η‖⁻¹ ^ 2 * ‖η‖ ^ 2 = 1 := by
    rw [← mul_pow,inv_mul_cancel₀ hn.ne',one_pow]
  calc
    (1/128:ℝ) * ‖η‖ ^ 2 ≤
        (‖η‖⁻¹ ^ 2 * ‖(p.val.val - conjugationOperator J p.val.val) η‖ ^ 2) * ‖η‖ ^ 2 := hm
    _ = ‖(p.val.val - conjugationOperator J p.val.val) η‖ ^ 2 := by
      calc
        _ = (‖η‖⁻¹ ^ 2 * ‖η‖ ^ 2) *
            ‖(p.val.val - conjugationOperator J p.val.val) η‖ ^ 2 := by ring
        _ = _ := by rw [hi,one_mul]

end

end KadisonKastler

end OAI
