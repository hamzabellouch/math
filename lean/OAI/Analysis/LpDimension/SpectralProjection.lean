import OAI.Analysis.LpDimension.HeatKernel

namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace
open scoped BigOperators Topology Matrix Matrix.Norms.Operator
universe u uE uI uV

namespace SubpolynomialLp

section ProjectionIntegral
variable {V : Type uV} [Fintype V] [DecidableEq V]

lemma exponential_sum_integral {I : Type uI} [Fintype I] (a b : I → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, a k = 0 → b k = 0) :
    IntegrableOn (fun t : ℝ => ∑ k, b k * Real.exp (-t * a k)) (Set.Ioi 0) ∧
      (∫ t in Set.Ioi (0 : ℝ), ∑ k, b k * Real.exp (-t * a k)) = ∑ k, b k / a k := by
  have hi (k : I) : IntegrableOn (fun t : ℝ => b k * Real.exp (-t * a k)) (Set.Ioi 0) := by
    by_cases hz : a k = 0
    · simp [hb k hz]
    · have hp : 0 < a k := lt_of_le_of_ne (ha k) (Ne.symm hz)
      have hh := (integrableOn_exp_mul_Ioi (neg_neg_of_pos hp) 0).const_mul (b k)
      have he : (fun t : ℝ => b k * Real.exp (-t * a k)) =
          (fun t : ℝ => b k * Real.exp (-a k * t)) := by
        funext t; congr 2; ring
      rw [he]
      exact hh
  refine ⟨integrable_finsetSum _ (fun k _ => hi k), ?_⟩
  rw [integral_finsetSum _ (fun k _ => hi k)]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hz : a k = 0
  · simp [hz, hb k hz]
  · have hp : 0 < a k := lt_of_le_of_ne (ha k) (Ne.symm hz)
    rw [integral_const_mul]
    have hh := integral_exp_mul_Ioi (neg_neg_of_pos hp) 0
    simp only [mul_zero, Real.exp_zero, neg_div_neg_eq] at hh
    have hexp : (fun t : ℝ => Real.exp (-t * a k)) =
        (fun t : ℝ => Real.exp (-a k * t)) := by funext t; congr 1; ring
    rw [hexp, hh]
    simp [div_eq_mul_inv]

section GramProjection
variable {E : Type uE} [Fintype E]

omit [DecidableEq V] in
theorem gramHermitian (A : Matrix E V ℝ) : (A.conjTranspose * A).IsHermitian :=
  (Matrix.posSemidef_conjTranspose_mul_self A).1

def gramEigenMatrix (A : Matrix E V ℝ) : Matrix E V ℝ :=
  A * ((gramHermitian A).eigenvectorUnitary : Matrix V V ℝ)

def gramProjection (A : Matrix E V ℝ) : Matrix E E ℝ :=
  gramEigenMatrix A * diagonal (fun k => ((gramHermitian A).eigenvalues k)⁻¹) *
    (gramEigenMatrix A).transpose

lemma gramEigenMatrix_zero (A : Matrix E V ℝ) (k : V)
    (hk : (gramHermitian A).eigenvalues k = 0) (e : E) : gramEigenMatrix A e k = 0 := by
  have hh := (gramHermitian A).mulVec_eigenvectorBasis k
  rw [hk, zero_smul] at hh
  have hz := (Matrix.conjTranspose_mul_self_mulVec_eq_zero A _).mp hh
  have hh' := congrFun hz e
  simpa only [gramEigenMatrix, Matrix.mul_apply, Matrix.IsHermitian.eigenvectorUnitary_apply,
    Matrix.mulVec, dotProduct, Pi.zero_apply] using hh'

lemma gram_heat_apply (A : Matrix E V ℝ) (t : ℝ) (e f : E) :
    (A * exp (-t • (A.conjTranspose * A)) * A.transpose) e f =
      ∑ k, (gramEigenMatrix A e k * gramEigenMatrix A f k) *
        Real.exp (-t * (gramHermitian A).eigenvalues k) := by
  rw [matrix_exp_spectral _ (gramHermitian A)]
  have he : A * ((gramHermitian A).eigenvectorUnitary : Matrix V V ℝ) *
      diagonal (fun k => Real.exp (-t * (gramHermitian A).eigenvalues k)) *
      (star ((gramHermitian A).eigenvectorUnitary : Matrix V V ℝ) * A.transpose) =
      gramEigenMatrix A * diagonal (fun k => Real.exp (-t * (gramHermitian A).eigenvalues k)) *
        (gramEigenMatrix A).transpose := by
    simp only [gramEigenMatrix, Matrix.transpose_mul, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc (_ * _ * _) _ A.transpose, he]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma gramProjection_heat_integral (A : Matrix E V ℝ) (e f : E) :
    IntegrableOn (fun t : ℝ => (A * exp (-t • (A.conjTranspose * A)) * A.transpose) e f)
      (Set.Ioi 0) ∧
    (∫ t in Set.Ioi (0 : ℝ), (A * exp (-t • (A.conjTranspose * A)) * A.transpose) e f) =
      gramProjection A e f := by
  have hh := exponential_sum_integral ((gramHermitian A).eigenvalues)
    (fun k => gramEigenMatrix A e k * gramEigenMatrix A f k)
    (Matrix.posSemidef_conjTranspose_mul_self A).eigenvalues_nonneg
    (fun k hk => by rw [gramEigenMatrix_zero A k hk e, zero_mul])
  simp_rw [gram_heat_apply]
  refine ⟨hh.1, hh.2.trans ?_⟩
  unfold gramProjection
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma gramEigenMatrix_gram (A : Matrix E V ℝ) :
    (gramEigenMatrix A).transpose * gramEigenMatrix A =
      diagonal (gramHermitian A).eigenvalues := by
  let U : Matrix V V ℝ := (gramHermitian A).eigenvectorUnitary
  have hU : U.transpose * U = 1 := by
    simpa only [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using Unitary.coe_star_mul_self (gramHermitian A).eigenvectorUnitary
  have hs : A.transpose * A = U * diagonal (gramHermitian A).eigenvalues * U.transpose := by
    calc
      _ = A.conjTranspose * A := by rw [Matrix.conjTranspose_eq_transpose_of_trivial]
      _ = _ := (gramHermitian A).spectral_theorem
      _ = U * diagonal (gramHermitian A).eigenvalues * U.transpose := by
        change U * diagonal (RCLike.ofReal ∘ (gramHermitian A).eigenvalues) * star U = _
        have he : (RCLike.ofReal ∘ (gramHermitian A).eigenvalues : V → ℝ) =
            (gramHermitian A).eigenvalues := rfl
        rw [he]
        congr 1
  change (A * U).transpose * (A * U) = _
  rw [Matrix.transpose_mul]
  calc
    _ = U.transpose * (A.transpose * A) * U := by simp only [Matrix.mul_assoc]
    _ = (U.transpose * U) * diagonal (gramHermitian A).eigenvalues * (U.transpose * U) := by
      rw [hs]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU, Matrix.one_mul, Matrix.mul_one]

lemma gramProjection_mul_eigenMatrix (A : Matrix E V ℝ) :
    gramProjection A * gramEigenMatrix A = gramEigenMatrix A := by
  unfold gramProjection
  rw [Matrix.mul_assoc, gramEigenMatrix_gram, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
  ext e k
  rw [Matrix.mul_diagonal]
  by_cases hk : (gramHermitian A).eigenvalues k = 0
  · rw [gramEigenMatrix_zero A k hk e, zero_mul]
  · rw [inv_mul_cancel₀ hk, mul_one]

lemma gramProjection_mul_self (A : Matrix E V ℝ) :
    gramProjection A * A = A := by
  let U : Matrix V V ℝ := (gramHermitian A).eigenvectorUnitary
  have hU : U * U.transpose = 1 := by
    simpa only [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      Unitary.coe_star] using Unitary.coe_mul_star_self (gramHermitian A).eigenvectorUnitary
  have he : gramEigenMatrix A * U.transpose = A := by
    change (A * U) * U.transpose = A
    rw [Matrix.mul_assoc, hU, Matrix.mul_one]
  calc
    _ = gramProjection A * (gramEigenMatrix A * U.transpose) := by rw [he]
    _ = gramEigenMatrix A * U.transpose := by rw [← Matrix.mul_assoc, gramProjection_mul_eigenMatrix]
    _ = A := he

lemma gramProjection_idempotent (A : Matrix E V ℝ) :
    gramProjection A * gramProjection A = gramProjection A := by
  conv_lhs => rhs; unfold gramProjection
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, gramProjection_mul_eigenMatrix]
  rfl

lemma gramProjection_symmetric (A : Matrix E V ℝ) : (gramProjection A).IsSymm := by
  show (gramProjection A).transpose = gramProjection A
  simp only [gramProjection, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.diagonal_transpose, Matrix.mul_assoc]

lemma mul_gramProjection_of_fix (P : Matrix E E ℝ) (A : Matrix E V ℝ)
    (hPA : P * A = A) : P * gramProjection A = gramProjection A := by
  simp only [gramProjection, gramEigenMatrix, ← Matrix.mul_assoc, hPA]

lemma gramProjection_eq_of_mutual_fix (A B : Matrix E V ℝ)
    (hAB : gramProjection A * B = B) (hBA : gramProjection B * A = A) :
    gramProjection A = gramProjection B := by
  have hab := mul_gramProjection_of_fix _ B hAB
  have hba := mul_gramProjection_of_fix _ A hBA
  have ht := congrArg Matrix.transpose hab
  rw [Matrix.transpose_mul, (gramProjection_symmetric A).eq,
    (gramProjection_symmetric B).eq] at ht
  exact hba.symm.trans ht

lemma gramProjection_right_diagonal (A : Matrix E V ℝ) (d : V → ℝ)
    (hd : ∀ i, d i ≠ 0) : gramProjection (A * diagonal d) = gramProjection A := by
  have he : (A * diagonal d) * diagonal (fun i => (d i)⁻¹) = A := by
    rw [Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
    have hh : (fun i => d i * (d i)⁻¹) = (fun _ : V => (1 : ℝ)) := by
      funext i; exact mul_inv_cancel₀ (hd i)
    rw [hh, Matrix.diagonal_one, Matrix.mul_one]
  apply gramProjection_eq_of_mutual_fix
  · calc
      _ = gramProjection (A * diagonal d) * ((A * diagonal d) * diagonal (fun i => (d i)⁻¹)) := by rw [he]
      _ = (A * diagonal d) * diagonal (fun i => (d i)⁻¹) := by
        rw [← Matrix.mul_assoc, gramProjection_mul_self]
      _ = A := he
  · rw [← Matrix.mul_assoc, gramProjection_mul_self]

end GramProjection
end ProjectionIntegral

end SubpolynomialLp

end

end OAI
