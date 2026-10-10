import OAI.Probability.InvariantIsing.Haar.HaarPolynomialRotation

namespace OAI

/-! Exponentiating an arbitrary real skew matrix in the physical group. -/
noncomputable section
open Matrix
open scoped Matrix Matrix.Norms.Frobenius
namespace InvariantIsing

def skewRotation {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.transpose = -A) (t : ℝ) : Orthogonal N :=
  ⟨NormedSpace.exp (t • A), NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (by
    rw [skewAdjoint.mem_iff]
    simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial,
      star_smul,star_trivial,smul_neg] using congrArg (fun M => t • M) hA)⟩

lemma skewRotation_det {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.transpose = -A) (t : ℝ) :
    (skewRotation A hA t : Matrix (Fin N) (Fin N) ℝ).det = 1 := by
  let f : ℝ → ℝ := fun s => (skewRotation A hA s : Matrix (Fin N) (Fin N) ℝ).det
  have hc : Continuous f := by
    apply Continuous.matrix_det
    exact continuous_iff_continuousAt.mpr fun s =>
      (hasDerivAt_exp_smul_const' A s).continuousAt
  have hm : Set.MapsTo f Set.univ ({1,-1} : Set ℝ) := by
    intro s _
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,f] using
      orthogonal_det_eq_one_or_neg_one (skewRotation A hA s)
  have he := isPreconnected_univ.constant_of_mapsTo
    (Set.toFinite ({1,-1} : Set ℝ)).isDiscrete hc.continuousOn hm (Set.mem_univ t)
      (Set.mem_univ (0:ℝ))
  simpa only [f,skewRotation,zero_smul,NormedSpace.exp_zero,Matrix.det_one] using he

def specialSkewRotation {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.transpose = -A) (t : ℝ) : SpecialOrthogonal N :=
  ⟨(skewRotation A hA t).val,Matrix.mem_specialOrthogonalGroup_iff.mpr
    ⟨(skewRotation A hA t).property,skewRotation_det A hA t⟩⟩

@[simp] lemma specialSkewRotation_zero {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.transpose = -A) : specialSkewRotation A hA 0 = 1 := by
  apply Subtype.ext
  simp [specialSkewRotation,skewRotation]

lemma hasDerivAt_specialSkewRotation {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.transpose = -A) (U : SpecialOrthogonal N) :
    HasDerivAt (fun t => ((specialSkewRotation A hA t*U : SpecialOrthogonal N) :
      Matrix (Fin N) (Fin N) ℝ)) (A*(U : Matrix (Fin N) (Fin N) ℝ)) 0 := by
  convert (hasDerivAt_exp_smul_const' A (0:ℝ)).mul_const
    (U : Matrix (Fin N) (Fin N) ℝ) using 1
  all_goals first | rfl | simp only [zero_smul,NormedSpace.exp_zero,mul_one]

lemma hasDerivAt_specialSkewRotation_polynomial {N : ℕ} (p : MatrixPolynomial N)
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.transpose = -A) (U : SpecialOrthogonal N) :
    HasDerivAt (fun t => matrixPolynomialEval
      ((specialSkewRotation A hA t*U : SpecialOrthogonal N) : Matrix (Fin N) (Fin N) ℝ) p)
      (matrixPolynomialEval (U : Matrix (Fin N) (Fin N) ℝ)
        (matrixPolynomialDerivation A p)) 0 := by
  have hd := hasDerivAt_specialSkewRotation A hA U
  have hh := hasDerivAt_matrixPolynomialEval p
    (fun t => ((specialSkewRotation A hA t*U : SpecialOrthogonal N) : Matrix (Fin N) (Fin N) ℝ))
    A 0 (fun i j => by
      rw [specialSkewRotation_zero,one_mul]
      convert (haarMatrixCoordinate i j).hasFDerivAt.comp_hasDerivAt 0 hd using 1 <;> rfl)
  simpa only [specialSkewRotation_zero,one_mul] using hh

end InvariantIsing

end

end OAI
