import Mathlib

namespace OAI

/-! Real Determinant Order. -/

section

 

noncomputable section
open Matrix Polynomial Filter Set
open scoped MatrixOrder Matrix.Norms.Elementwise
namespace PotentialABP
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma real_trace_mul_nonneg {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A*B).trace := by
  let S := CFC.sqrt A
  have hS : S.PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have hsquare : S*S = A := by simpa [S, pow_two] using CFC.sq_sqrt A hA.nonneg
  have htr := (hB.mul_mul_conjTranspose_same S).trace_nonneg
  have he : (S*B*Sᴴ).trace = (A*B).trace := by
    rw [hS.isHermitian.eq, Matrix.trace_mul_cycle, hsquare]
  rwa [he] at htr

lemma real_hasDerivAt_det_one_add_smul (M : Matrix n n ℝ) :
    HasDerivAt (fun t : ℝ => (1+t • M).det) M.trace 0 := by
  have hp := (Matrix.det (1 + (Polynomial.X : ℝ[X]) • M.map Polynomial.C)).hasDerivAt (0 : ℝ)
  rw [Matrix.derivative_det_one_add_X_smul] at hp
  simpa [eval_det, ← Matrix.smul_eq_mul_diagonal] using hp

lemma real_hasDerivAt_det_add_smul (H K : Matrix n n ℝ) (hH : IsUnit H.det) :
    HasDerivAt (fun t : ℝ => (H+t • K).det) (H.det*(H⁻¹*K).trace) 0 := by
  have hd := (real_hasDerivAt_det_one_add_smul (H⁻¹*K)).const_mul H.det
  apply hd.congr_of_eventuallyEq
  filter_upwards [] with t
  rw [← Matrix.det_mul]
  congr 1
  simp [Matrix.mul_add, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hH]

lemma real_hasDerivAt_det_shift (A B : Matrix n n ℝ) (t : ℝ)
    (ht : (A+t • B).PosDef) :
    HasDerivAt (fun s : ℝ => (A+s • B).det)
      ((A+t • B).det*((A+t • B)⁻¹*B).trace) t := by
  have hd := real_hasDerivAt_det_add_smul (A+t • B) B
    (isUnit_iff_ne_zero.mpr ht.det_pos.ne')
  have hc := hd.comp_of_eq t ((hasDerivAt_id t).sub_const t) (by simp)
  simp only [mul_one] at hc
  apply hc.congr_of_eventuallyEq
  filter_upwards [] with s
  dsimp only [Function.comp_apply,id_eq]
  simp only [sub_smul]
  congr 1
  abel

lemma real_det_add_posSemidef (A B : Matrix n n ℝ) (hA : A.PosDef) (hB : B.PosSemidef) :
    A.det ≤ (A+B).det := by
  let f : ℝ → ℝ := fun t => (A+t • B).det
  have hp (t : ℝ) (ht : 0 ≤ t) : (A+t • B).PosDef := hA.add_posSemidef (hB.smul ht)
  have hd (t : ℝ) (ht : 0 ≤ t) := real_hasDerivAt_det_shift A B t (hp t ht)
  have hm : MonotoneOn f (Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · intro t ht
      exact (hd t ht.1).continuousAt.continuousWithinAt
    · intro t ht
      exact (hd t (interior_subset ht).1).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd t (interior_subset ht).1).deriv]
      exact mul_nonneg (hp t (interior_subset ht).1).det_pos.le
        (real_trace_mul_nonneg (hp t (interior_subset ht).1).inv.posSemidef hB)
  simpa [f] using hm (show (0:ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    (show (1:ℝ) ∈ Icc 0 1 by constructor <;> norm_num) (by norm_num)

lemma real_det_mono {A B : Matrix n n ℝ} (hA : A.PosSemidef)
    (hBA : (B-A).PosSemidef) : A.det ≤ B.det := by
  by_cases ha : A.det = 0
  · rw [ha]
    have hb : B.PosSemidef := by simpa using hA.add hBA
    exact hb.det_nonneg
  · simpa using real_det_add_posSemidef A (B-A)
      (hA.posDef_iff_det_ne_zero.mpr ha) hBA

end PotentialABP

end
end

end OAI
