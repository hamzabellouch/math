import Mathlib
import OAI.Geometry.PrescribedPotential.AnalyticSupport

namespace OAI

/-! Determinant Order. -/

section

 

noncomputable section
open Matrix Filter Set
open scoped ComplexOrder MatrixOrder Classical
namespace MongeAmpere
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma hasDerivAt_det_real_shift (A B : Matrix n n ℂ) (t : ℝ)
    (ht : (A + (t : ℂ) • B).PosDef) :
    HasDerivAt (fun s : ℝ => (A + (s : ℂ) • B).det.re)
      ((A + (t : ℂ) • B).det * ((A + (t : ℂ) • B)⁻¹ * B).trace).re t := by
  have hd := (hasDerivAt_det_add_smul (A + (t : ℂ) • B) B
    (isUnit_iff_ne_zero.mpr ht.det_pos.ne')).real_of_complex
  have hc := hd.comp_of_eq t ((hasDerivAt_id t).sub_const t) (by simp)
  simp only [mul_one] at hc
  apply hc.congr_of_eventuallyEq
  filter_upwards [] with s
  dsimp only [Function.comp_apply, id_eq]
  simp only [Complex.ofReal_sub, sub_smul]
  congr 2
  abel

lemma det_re_add_posSemidef (A B : Matrix n n ℂ) (hA : A.PosDef) (hB : B.PosSemidef) :
    A.det.re ≤ (A+B).det.re := by
  let f : ℝ → ℝ := fun t => (A + (t : ℂ) • B).det.re
  have hp (t : ℝ) (ht : 0 ≤ t) : (A + (t : ℂ) • B).PosDef :=
    hA.add_posSemidef (hB.smul (Complex.nonneg_iff.mpr ⟨ht,rfl⟩))
  have hd (t : ℝ) (ht : 0 ≤ t) := hasDerivAt_det_real_shift A B t (hp t ht)
  have hm : MonotoneOn f (Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · intro t ht
      exact (hd t ht.1).continuousAt.continuousWithinAt
    · intro t ht
      exact (hd t (interior_subset ht).1).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd t (interior_subset ht).1).deriv]
      have hdet := Complex.pos_iff.mp (hp t (interior_subset ht).1).det_pos
      rw [Complex.mul_re, hdet.2.symm, zero_mul, sub_zero]
      exact mul_nonneg hdet.1.le (EllipticKernel.trace_mul_nonneg
        (hp t (interior_subset ht).1).inv.posSemidef hB)
  simpa [f] using hm (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num) (by norm_num)

lemma det_re_mono {A B : Matrix n n ℂ} (hA : A.PosDef) (hBA : (B-A).PosSemidef) :
    A.det.re ≤ B.det.re := by
  simpa using det_re_add_posSemidef A (B-A) hA hBA
end MongeAmpere

end
end

end OAI
