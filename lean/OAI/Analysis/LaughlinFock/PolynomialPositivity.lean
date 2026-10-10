import Mathlib

namespace OAI

/-! Polynomial Positivity. -/
noncomputable section
namespace LaughlinFock
open scoped Matrix ComplexOrder BigOperators
open Polynomial

 

theorem polynomial_eval_pos_of_nonneg_coeffs (p : ℝ[X]) (hp : p ≠ 0)
    (hcoeff : ∀ b, 0 ≤ p.coeff b) {x : ℝ} (hx : 0 < x) : 0 < p.eval x := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum]
  obtain ⟨b, hb⟩ := Polynomial.support_nonempty.mpr hp
  exact Finset.sum_pos'
    (fun c _ => mul_nonneg (hcoeff c) (pow_nonneg hx.le c))
    ⟨b, hb, mul_pos (lt_of_le_of_ne (hcoeff b)
      (Ne.symm (Polynomial.mem_support_iff.mp hb))) (pow_pos hx b)⟩

 

theorem symmetric_posSemidef_of_charpoly_coeffs {ι : Type*}
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (hM : M.IsHermitian)
    (hcoeff : ∀ b, 0 ≤ (-M).charpoly.coeff b) : M.PosSemidef := by
  apply hM.posSemidef_iff_eigenvalues_nonneg.mpr
  intro i
  by_contra hi
  have hi' : 0 < -hM.eigenvalues i := neg_pos.mpr (lt_of_not_ge hi)
  have hspec : -hM.eigenvalues i ∈ spectrum ℝ (-M) := by
    rw [← spectrum.neg_eq]
    simpa only [Set.mem_neg, neg_neg] using hM.eigenvalues_mem_spectrum_real i
  have hz := (Matrix.mem_spectrum_iff_isRoot_charpoly.mp hspec).eq_zero
  have hp := polynomial_eval_pos_of_nonneg_coeffs (-M).charpoly
    (-M).charpoly_monic.ne_zero hcoeff hi'
  exact (ne_of_gt hp) hz

 

theorem real_matrix_posSemidef_complex {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.PosSemidef) :
    (M.map (algebraMap ℝ ℂ)).PosSemidef := by
  have hH : (M.map (algebraMap ℝ ℂ)).IsHermitian := by
    apply Matrix.IsHermitian.ext_iff.mpr
    intro i j
    have h := Matrix.IsHermitian.ext_iff.mp hM.isHermitian i j
    simpa using congrArg (algebraMap ℝ ℂ) h
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro x
  have hRe := hM.dotProduct_mulVec_nonneg (fun i => (x i).re)
  have hIm := hM.dotProduct_mulVec_nonneg (fun i => (x i).im)
  apply Complex.nonneg_iff.mpr
  constructor
  · have he : (star x ⬝ᵥ (M.map (algebraMap ℝ ℂ) *ᵥ x)).re =
        (fun i => (x i).re) ⬝ᵥ (M *ᵥ fun i => (x i).re) +
        (fun i => (x i).im) ⬝ᵥ (M *ᵥ fun i => (x i).im) := by
      simp [dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.sum_add_distrib,
        Complex.mul_re, Complex.mul_im, Finset.mul_sum]
    rw [he]
    simpa only [star_trivial, Pi.star_apply] using add_nonneg hRe hIm
  · exact (hH.im_star_dotProduct_mulVec_self x).symm

 

theorem rational_posSemidef_of_charpoly_coeffs {ι : Type*}
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℚ) (hM : M.IsSymm)
    (hcoeff : ∀ b, 0 ≤ (-M).charpoly.coeff b) :
    (M.map (algebraMap ℚ ℂ)).PosSemidef := by
  let N : Matrix ι ι ℝ := M.map (algebraMap ℚ ℝ)
  have hN : N.IsHermitian := by
    rw [Matrix.isHermitian_iff_isSymm]
    show Nᵀ = N
    change (M.map (algebraMap ℚ ℝ))ᵀ = M.map (algebraMap ℚ ℝ)
    rw [← Matrix.transpose_map, hM]
  have hC (b : ℕ) : 0 ≤ (-N).charpoly.coeff b := by
    have hneg : -N = (-M).map (algebraMap ℚ ℝ) := by
      ext i j
      simp [N]
    rw [hneg, Matrix.charpoly_map, Polynomial.coeff_map]
    change 0 ≤ ((-M).charpoly.coeff b : ℝ)
    exact_mod_cast hcoeff b
  have hP := real_matrix_posSemidef_complex N
    (symmetric_posSemidef_of_charpoly_coeffs N hN hC)
  convert hP using 1
  ext i j
  simp [N]

 

theorem certificate_diagonal_congruence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Y Z : Matrix ι ι ℝ) (u c : ι → ℝ) (hu : ∀ r, 0 ≤ u r) :
    let D := Matrix.diagonal (fun r => Real.sqrt (u r))
    let E := D * Y * D
    let G := D * Z * D
    G * (Matrix.diagonal c - E) * G =
      D * (Z * (Matrix.diagonal (fun r => c r * u r) -
        Matrix.diagonal u * Y * Matrix.diagonal u) * Z) * D := by
  dsimp only
  let D := Matrix.diagonal (fun r => Real.sqrt (u r))
  have hDD : D * D = Matrix.diagonal u := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext r
    exact Real.mul_self_sqrt (hu r)
  have hc : D * Matrix.diagonal c * D =
      Matrix.diagonal (fun r => c r * u r) := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext r
    rw [mul_right_comm, Real.mul_self_sqrt (hu r)]
    exact mul_comm _ _
  change (D * Z * D) * (Matrix.diagonal c - D * Y * D) * (D * Z * D) = _
  calc
    _ = D * (Z * (D * Matrix.diagonal c * D - (D * D) * Y * (D * D)) * Z) * D := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    _ = _ := by rw [hDD, hc]

 

theorem certificate_compression_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Y Z : Matrix ι ι ℝ) (u c : ι → ℝ) (hu : ∀ r, 0 ≤ u r)
    (hM : (Z * (Matrix.diagonal (fun r => c r * u r) -
        Matrix.diagonal u * Y * Matrix.diagonal u) * Z).IsHermitian)
    (hcoeff : ∀ b, 0 ≤ (-(Z * (Matrix.diagonal (fun r => c r * u r) -
        Matrix.diagonal u * Y * Matrix.diagonal u) * Z)).charpoly.coeff b) :
    let D := Matrix.diagonal (fun r => Real.sqrt (u r))
    let E := D * Y * D
    let G := D * Z * D
    (G * (Matrix.diagonal c - E) * G).PosSemidef := by
  dsimp only
  rw [certificate_diagonal_congruence Y Z u c hu]
  have h := symmetric_posSemidef_of_charpoly_coeffs _ hM hcoeff
  simpa only [Matrix.diagonal_conjTranspose, star_trivial] using
    h.mul_mul_conjTranspose_same (Matrix.diagonal (fun r => Real.sqrt (u r)))

end LaughlinFock
end

end OAI
