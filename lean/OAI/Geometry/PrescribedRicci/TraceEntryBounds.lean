import Mathlib
import OAI.Geometry.PrescribedRicci.KaehlerTrace
import OAI.Geometry.PrescribedRicci.TraceCauchySchwarz

namespace OAI

/-! Trace Entry Bounds. -/

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
namespace MongeAmpere
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma trace_single_quadratic (B K : Matrix n n ℂ) (i j : n) :
    (B*(Matrix.single i j 1)ᴴ*K*Matrix.single i j 1).trace = K i i*B j j := by
  rw [Matrix.conjTranspose_single]
  simp only [star_one]
  rw [mul_assoc B (Matrix.single j i 1),mul_assoc B (Matrix.single j i 1*K),
    Matrix.single_mul_mul_single,one_mul,mul_one,Matrix.trace_mul_single]
  simp only [op_smul_eq_mul]
  exact mul_comm _ _

lemma entry_sq_le_relative_trace (B G : Matrix n n ℂ) (hB : B.PosSemidef)
    (hG : G.PosDef) (i j : n) :
    ‖B j i‖^2 ≤ (B*G).trace.re * (G⁻¹ i i).re * (B j j).re := by
  have hc := trace_cauchySchwarz B G (Matrix.single i j 1) hB hG
  rw [Matrix.trace_mul_single,op_smul_eq_mul,mul_one,trace_single_quadratic] at hc
  have him := (Complex.nonneg_iff.mp (hG.inv.posSemidef.diag_nonneg (i:=i))).2.symm
  simpa only [Complex.mul_re,him,zero_mul,sub_zero,mul_assoc] using hc

lemma diag_le_relative_trace (B G : Matrix n n ℂ) (hB : B.PosDef)
    (hG : G.PosDef) (i : n) :
    (B i i).re ≤ (B*G).trace.re * (G⁻¹ i i).re := by
  have hb := (Complex.pos_iff.mp (hB.diag_pos (i:=i))).1
  have hc := entry_sq_le_relative_trace B G hB.posSemidef hG i i
  have hi := (Complex.pos_iff.mp (hB.diag_pos (i:=i))).2.symm
  rw [Complex.sq_norm,Complex.normSq_apply,hi,mul_zero,add_zero] at hc
  nlinarith

lemma entry_le_relative_trace [Nonempty n] (B G : Matrix n n ℂ)
    (hB : B.PosDef) (hG : G.PosDef) {M : ℝ} (hM : 0 ≤ M)
    (hdiag : ∀ i, (G⁻¹ i i).re ≤ M) (i j : n) :
    ‖B i j‖ ≤ M*(B*G).trace.re := by
  have hs := (trace_mul_pos hB hG).le
  have hb := (Complex.pos_iff.mp (hB.diag_pos (i:=i))).1.le
  have hd := diag_le_relative_trace B G hB hG i
  have hd' : (B i i).re ≤ M*(B*G).trace.re := by
    calc
      _ ≤ (B*G).trace.re*(G⁻¹ i i).re := hd
      _ ≤ (B*G).trace.re*M := mul_le_mul_of_nonneg_left (hdiag i) hs
      _ = _ := mul_comm _ _
  have hc := entry_sq_le_relative_trace B G hB.posSemidef hG j i
  have hx : (B*G).trace.re*(G⁻¹ j j).re*(B i i).re ≤ (M*(B*G).trace.re)^2 := by
    calc
      _ ≤ ((B*G).trace.re*M)*(B i i).re := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hdiag j) hs) hb
      _ ≤ ((B*G).trace.re*M)*(M*(B*G).trace.re) := mul_le_mul_of_nonneg_left hd' (mul_nonneg hs hM)
      _ = _ := by ring
  have hpos := mul_nonneg hM hs
  nlinarith [norm_nonneg (B i j)]

end MongeAmpere

end

end OAI
