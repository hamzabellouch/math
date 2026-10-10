import OAI.Geometry.EinsteinFour.DeterminantCompression
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace OAI

/-! The finite-dimensional logarithmic determinant series used by the
lower radial comparison. It applies to the scalar Green matrix and its
three-dimensional curvature perturbation. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem trace_unitary_conjugation (U : Matrix.unitaryGroup ι ℝ)
    (A : Matrix ι ι ℝ) :
    (Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U A).trace = A.trace := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]

private theorem det_unitary_conjugation (U : Matrix.unitaryGroup ι ℝ)
    (A : Matrix ι ι ℝ) :
    (Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U A).det = A.det := by
  have hU := congrArg Matrix.det (Unitary.coe_star_mul_self U)
  simp only [Matrix.det_mul, Matrix.det_one] at hU
  rw [Unitary.conjStarAlgAut_apply, Matrix.det_mul, Matrix.det_mul]
  calc
    _ = ((star U : Matrix ι ι ℝ).det * (U : Matrix ι ι ℝ).det) * A.det := by ring
    _ = A.det := by rw [hU, one_mul]

theorem trace_pow_eq_sum_eigenvalues {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (k : ℕ) : (A ^ k).trace = ∑ i, hA.eigenvalues i ^ k := by
  let φ := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) (star hA.eigenvectorUnitary)
  have hd : φ A = diagonal hA.eigenvalues := by
    simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hA.conjStarAlgAut_star_eigenvectorUnitary
  calc
    _ = (φ (A ^ k)).trace := (trace_unitary_conjugation _ _).symm
    _ = (diagonal hA.eigenvalues ^ k).trace := by rw [map_pow, hd]
    _ = _ := by simp only [diagonal_pow, Matrix.trace_diagonal, Pi.pow_apply]

private theorem one_sub_eigenvalues_pos {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hI : (1 - A).PosDef) : ∀ i, 0 < 1 - hA.eigenvalues i := by
  let U := star hA.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U
  have hd : φ A = diagonal hA.eigenvalues := by
    simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hA.conjStarAlgAut_star_eigenvectorUnitary
  have hunit : IsUnit (star (U : Matrix ι ι ℝ)) := (Unitary.isUnit_coe (U := U)).star
  have hp : ((star (U : Matrix ι ι ℝ))ᴴ * (1 - A) *
      star (U : Matrix ι ι ℝ)).PosDef :=
    hI.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hunit)
  have he : φ (1 - A) = diagonal (fun i => 1 - hA.eigenvalues i) := by
    rw [map_sub, map_one, hd]
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hp' : (φ (1 - A)).PosDef := by
    simpa only [φ, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose] using hp
  rw [he, Matrix.posDef_diagonal_iff] at hp'
  exact hp'

theorem log_det_one_sub_eq_sum {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hI : (1 - A).PosDef) :
    Real.log (1 - A).det = ∑ i, Real.log (1 - hA.eigenvalues i) := by
  let φ := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) (star hA.eigenvectorUnitary)
  have hd : φ A = diagonal hA.eigenvalues := by
    simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hA.conjStarAlgAut_star_eigenvectorUnitary
  have he : φ (1 - A) = diagonal (fun i => 1 - hA.eigenvalues i) := by
    rw [map_sub, map_one, hd]
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [← det_unitary_conjugation (star hA.eigenvectorUnitary), he, Matrix.det_diagonal]
  exact Real.log_prod (fun i _ => (one_sub_eigenvalues_pos hA hI i).ne')

/-- The full logarithmic determinant is the sum of ordered matrix moments. -/
theorem hasSum_trace_pow_neg_log_det {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hI : (1 - A).PosDef) :
    HasSum (fun k : ℕ => (A ^ (k + 1)).trace / (k + 1))
      (-Real.log (1 - A).det) := by
  have hs (i : ι) : HasSum
      (fun k : ℕ => hA.isHermitian.eigenvalues i ^ (k + 1) / (k + 1))
      (-Real.log (1 - hA.isHermitian.eigenvalues i)) :=
    Real.hasSum_pow_div_log_of_abs_lt_one (by
      rw [abs_of_nonneg (hA.eigenvalues_nonneg i)]
      linarith [one_sub_eigenvalues_pos hA.isHermitian hI i])
  have H := hasSum_sum (s := Finset.univ) (fun i _ => hs i)
  convert H using 1
  · ext k
    rw [trace_pow_eq_sum_eigenvalues hA.isHermitian, Finset.sum_div]
  · rw [log_det_one_sub_eq_sum hA.isHermitian hI, Finset.sum_neg_distrib]

end
end PositiveEinsteinFour.Jacobi

end OAI
