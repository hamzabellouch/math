import Mathlib
import OAI.Geometry.PrescribedPotential.AnalyticSupport

namespace OAI

/-! Trace Cauchy Schwarz. -/

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
namespace MongeAmpere
variable {n : Type*} [Fintype n] [DecidableEq n]

@[instance_reducible] def tracePairCore (B K : Matrix n n ℂ) (hB : B.PosSemidef) (hK : K.PosSemidef) :
    PreInnerProductSpace.Core ℂ (Matrix n n ℂ) where
  inner U V := (B*Uᴴ*K*V).trace
  conj_inner_symm U V := by
    change star (B*Vᴴ*K*U).trace = _
    rw [← trace_conjTranspose]
    simp only [conjTranspose_mul,conjTranspose_conjTranspose,hB.isHermitian.eq,hK.isHermitian.eq]
    simp only [← mul_assoc]
    simpa only [mul_assoc] using (Matrix.trace_mul_comm (Uᴴ*K*V) B)
  re_inner_nonneg U := by
    change 0 ≤ (B*Uᴴ*K*U).trace.re
    simpa only [mul_assoc] using
      EllipticKernel.trace_mul_nonneg hB (hK.conjTranspose_mul_mul_same U)
  add_left U V W := by simp only [conjTranspose_add,mul_add,add_mul,trace_add]
  smul_left U V c := by simp only [conjTranspose_smul,Matrix.mul_smul,Matrix.smul_mul,trace_smul,smul_eq_mul]; rfl

lemma trace_cauchySchwarz (B G W : Matrix n n ℂ) (hB : B.PosSemidef)
    (hG : G.PosDef) :
    ‖(B*W).trace‖^2 ≤ (B*G).trace.re * (B*Wᴴ*G⁻¹*W).trace.re := by
  let := tracePairCore B G⁻¹ hB hG.inv.posSemidef
  have hh := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) G W
  have hunit : IsUnit G.det := isUnit_iff_ne_zero.mpr hG.det_pos.ne'
  have h1 : (B*Gᴴ*G⁻¹*W).trace = (B*W).trace := by
    rw [hG.isHermitian.eq,mul_assoc B G,Matrix.mul_nonsing_inv G hunit,mul_one]
  have h2 : (B*Wᴴ*G⁻¹*G).trace = star (B*W).trace := by
    rw [mul_assoc (B*Wᴴ),Matrix.nonsing_inv_mul G hunit,mul_one,← trace_conjTranspose]
    rw [conjTranspose_mul,hB.isHermitian.eq,trace_mul_comm]
  have h3 : (B*Gᴴ*G⁻¹*G).trace = (B*G).trace := by
    rw [hG.isHermitian.eq,mul_assoc B G,Matrix.mul_nonsing_inv G hunit,mul_one]
  change ‖(B*Gᴴ*G⁻¹*W).trace‖ * ‖(B*Wᴴ*G⁻¹*G).trace‖ ≤
    (B*Gᴴ*G⁻¹*G).trace.re * (B*Wᴴ*G⁻¹*W).trace.re at hh
  simpa only [h1,h2,h3,norm_star,pow_two] using hh

end MongeAmpere

end

end OAI
