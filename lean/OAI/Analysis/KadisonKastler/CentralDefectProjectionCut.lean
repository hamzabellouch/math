import OAI.Analysis.KadisonKastler.SelfAdjointCentralGap

namespace OAI

/-! # Projection cuts from general approximately central contractions

Real and imaginary parts reduce the contraction to the self-adjoint
spectral-cut argument. The constants retain a uniform positive gap.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem exists_projection_gap_of_central_defect
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ η : H) (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) (hJξ : J ξ = ξ)
    (a : Algebra M) (ha : ‖a‖ ≤ 1) (δ : ℝ) (hδ : 0 < δ)
    (hsmall : ‖centralVectorDefect J ξ a.val‖ < δ / 64)
    (hgap : (1 / 2 : ℝ) ≤ ‖centralVectorDefect J η a.val‖) :
    ∃ p : AlgebraProjection M,
      ‖(p.val.val - conjugationOperator J p.val.val) ξ‖ ^ 2 ≤ δ ∧
      (1 / 128 : ℝ) ≤ ‖(p.val.val - conjugationOperator J p.val.val) η‖ ^ 2 := by
  obtain ⟨b,hbs,hbn,hbsmall,hbgap⟩ := exists_selfAdjoint_central_gap J hJ ξ η hJξ a
  have hbstar : star b.val = b.val := congrArg Subtype.val hbs.star_eq
  have hbe (ζ : H) : centralVectorDefect J ζ b.val = (b.val - conjugationOperator J b.val) ζ := by
    rw [centralVectorDefect_apply,hbstar]
    rfl
  rw [hbe] at hbsmall hbgap
  apply exists_selfAdjoint_projection_cut J hJ hright b hbs (hbn.trans ha) ξ η hη δ
    (1 / 128) hδ (by norm_num)
  rw [hξ,mul_one]
  have htest : (1 / 4 : ℝ) ≤ ‖(b.val - conjugationOperator J b.val) η‖ := by linarith
  have hroom : (1 / 64 : ℝ) ≤ ‖(b.val - conjugationOperator J b.val) η‖ ^ 2 / 2 -
      2 * (1 / 128 : ℝ) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hroom hδ.le
  have hreference := hbsmall.trans_lt hsmall
  nlinarith

end

end KadisonKastler

end OAI
