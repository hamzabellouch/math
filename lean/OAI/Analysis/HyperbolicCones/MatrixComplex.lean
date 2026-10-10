import OAI.Analysis.HyperbolicCones.MatrixLinear
import OAI.Analysis.HyperbolicCones.PolynomialEvaluation

namespace OAI

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open Matrix

namespace Paper256

theorem isHermitian_complexify {n : ℕ} (A : Mat n ℝ) (hA : A.IsHermitian) :
    (A.map Complex.ofReal).IsHermitian :=
  hA.map _ (by intro x; simp)

theorem complex_quadratic_re {n : ℕ} (A : Mat n ℝ) (w : Fin n → ℂ) :
    (dotProduct (star w) (A.map Complex.ofReal *ᵥ w)).re =
      dotProduct (fun i => (w i).re) (A *ᵥ fun i => (w i).re) +
      dotProduct (fun i => (w i).im) (A *ᵥ fun i => (w i).im) := by
  have ht (i j : Fin n) : (star (w i) * ((A i j : ℂ) * w j)).re =
      (w i).re * (A i j * (w j).re) + (w i).im * (A i j * (w j).im) := by
    simp [Complex.mul_re, Complex.mul_im]
  simp only [dotProduct, mulVec, Matrix.map_apply, Pi.star_apply, Finset.mul_sum,
    Complex.re_sum, ht, Finset.sum_add_distrib]

theorem posSemidef_complexify {n : ℕ} (A : Mat n ℝ) (hA : A.PosSemidef) :
    (A.map Complex.ofReal).PosSemidef := by
  have hh := isHermitian_complexify A hA.isHermitian
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hh
  intro w
  apply RCLike.nonneg_iff.2
  refine ⟨?_, hh.im_star_dotProduct_mulVec_self w⟩
  rw [show RCLike.re (dotProduct (star w) (A.map Complex.ofReal *ᵥ w)) =
    (dotProduct (star w) (A.map Complex.ofReal *ᵥ w)).re from rfl, complex_quadratic_re]
  exact add_nonneg (by simpa using hA.dotProduct_mulVec_nonneg (fun i => (w i).re))
    (by simpa using hA.dotProduct_mulVec_nonneg (fun i => (w i).im))

theorem posDef_complexify {n : ℕ} (A : Mat n ℝ) (hA : A.PosDef) :
    (A.map Complex.ofReal).PosDef := by
  have hh := isHermitian_complexify A hA.isHermitian
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hh
  intro w hw
  apply RCLike.pos_iff.2
  refine ⟨?_, hh.im_star_dotProduct_mulVec_self w⟩
  change 0 < (dotProduct (star w) (A.map Complex.ofReal *ᵥ w)).re
  rw [complex_quadratic_re]
  by_cases hr : (fun i => (w i).re) = 0
  · have hi : (fun i => (w i).im) ≠ 0 := by
      intro hi
      apply hw
      funext i
      apply Complex.ext
      · exact congrFun hr i
      · exact congrFun hi i
    exact add_pos_of_nonneg_of_pos
      (by simpa using hA.posSemidef.dotProduct_mulVec_nonneg (fun i => (w i).re))
      (by simpa using hA.dotProduct_mulVec_pos hi)
  · exact add_pos_of_pos_of_nonneg (by simpa using hA.dotProduct_mulVec_pos hr)
      (by simpa using hA.posSemidef.dotProduct_mulVec_nonneg (fun i => (w i).im))

theorem complex_resolvent_isUnit {n : ℕ} (A : Mat n ℝ) (hA : A.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) : IsUnit (z • (1 : Mat n ℂ) - A.map Complex.ofReal) := by
  by_contra hn
  apply hz
  apply (isHermitian_complexify A hA).isSelfAdjoint.im_eq_zero_of_mem_spectrum
  simpa only [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one] using hn

end Paper256

end

end OAI
