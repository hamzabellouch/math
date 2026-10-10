import OAI.Probability.InvariantIsing.Cavity.CavityGaussianBasis

namespace OAI

/-! Square completion for an arbitrary positive definite real precision
matrix, expressed against the standard finite-dimensional Gaussian. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix

namespace InvariantIsing

lemma cavity_eigenbasis_action {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsHermitian) (i : Fin d) :
    Q.toEuclideanLin (hQ.eigenvectorBasis i) =
      hQ.eigenvalues i • hQ.eigenvectorBasis i := by
  ext j
  exact congrFun (hQ.mulVec_eigenvectorBasis i) j

lemma cavity_eigenbasis_coordinate {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsHermitian) (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    hQ.eigenvectorBasis.repr (Q.toEuclideanLin x) i =
      hQ.eigenvalues i * hQ.eigenvectorBasis.repr x i := by
  rw [hQ.eigenvectorBasis.repr_apply_apply, hQ.eigenvectorBasis.repr_apply_apply,
    ← Matrix.isSymmetric_toEuclideanLin_iff.mpr hQ (hQ.eigenvectorBasis i) x,
    cavity_eigenbasis_action Q hQ i, real_inner_smul_left]

lemma cavity_eigenbasis_quadratic {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsHermitian) (x : EuclideanSpace ℝ (Fin d)) :
    ⟪x, Q.toEuclideanLin x⟫ =
      ∑ i, hQ.eigenvalues i * (hQ.eigenvectorBasis.repr x i) ^ 2 := by
  rw [← hQ.eigenvectorBasis.sum_inner_mul_inner x (Q.toEuclideanLin x)]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm (hQ.eigenvectorBasis i) x, ← hQ.eigenvectorBasis.repr_apply_apply,
    ← hQ.eigenvectorBasis.repr_apply_apply, cavity_eigenbasis_coordinate]
  ring

lemma cavity_eigenbasis_linear {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsHermitian) (l x : EuclideanSpace ℝ (Fin d)) :
    ⟪l, x⟫ = ∑ i, hQ.eigenvectorBasis.repr l i * hQ.eigenvectorBasis.repr x i := by
  rw [← hQ.eigenvectorBasis.sum_inner_mul_inner l x]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm (hQ.eigenvectorBasis i) l, hQ.eigenvectorBasis.repr_apply_apply,
    hQ.eigenvectorBasis.repr_apply_apply]

lemma cavity_eigenbasis_exponent {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsHermitian) (l x : EuclideanSpace ℝ (Fin d)) :
    (‖x‖ ^ 2 - ⟪x, Q.toEuclideanLin x⟫) / 2 + ⟪l, x⟫ =
      ∑ i, ((1 - hQ.eigenvalues i) / 2 * (hQ.eigenvectorBasis.repr x i) ^ 2 +
        hQ.eigenvectorBasis.repr l i * hQ.eigenvectorBasis.repr x i) := by
  rw [cavity_eigenbasis_quadratic Q hQ, cavity_eigenbasis_linear Q hQ]
  have hn : ‖x‖ ^ 2 = ∑ i, (hQ.eigenvectorBasis.repr x i) ^ 2 := by
    simpa only [hQ.eigenvectorBasis.repr_apply_apply] using
      (hQ.eigenvectorBasis.sum_sq_inner_right x).symm
  rw [hn, ← Finset.sum_sub_distrib, Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma cavity_precision_inverse_cancel {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.PosDef) (l : EuclideanSpace ℝ (Fin d)) :
    Q.toEuclideanLin (Q⁻¹.toEuclideanLin l) = l := by
  ext i
  change (Q *ᵥ (Q⁻¹ *ᵥ fun j => l j)) i = l i
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Q
    (isUnit_iff_ne_zero.mpr hQ.det_pos.ne'), Matrix.one_mulVec]

lemma cavity_eigenbasis_inverse_coordinate {d : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosDef)
    (l : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    hQ.1.eigenvectorBasis.repr (Q⁻¹.toEuclideanLin l) i =
      hQ.1.eigenvectorBasis.repr l i / hQ.1.eigenvalues i := by
  have hc := cavity_eigenbasis_coordinate Q hQ.1 (Q⁻¹.toEuclideanLin l) i
  rw [cavity_precision_inverse_cancel Q hQ l] at hc
  apply (eq_div_iff (hQ.eigenvalues_pos i).ne').2
  simpa only [mul_comm] using hc.symm

lemma cavity_eigenbasis_inverse_quadratic {d : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosDef)
    (l : EuclideanSpace ℝ (Fin d)) :
    ⟪l, Q⁻¹.toEuclideanLin l⟫ =
      ∑ i, (hQ.1.eigenvectorBasis.repr l i) ^ 2 / hQ.1.eigenvalues i := by
  rw [cavity_eigenbasis_linear Q hQ.1]
  apply Finset.sum_congr rfl
  intro i _
  rw [cavity_eigenbasis_inverse_coordinate Q hQ l i]
  ring

lemma cavity_precision_normalizer {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.PosDef) :
    (∏ i, (Real.sqrt (hQ.1.eigenvalues i))⁻¹) = (Real.sqrt Q.det)⁻¹ := by
  rw [Finset.prod_inv_distrib, hQ.1.det_eq_prod_eigenvalues]
  change (∏ i, Real.sqrt (hQ.1.eigenvalues i))⁻¹ =
    (Real.sqrt (∏ i, hQ.1.eigenvalues i))⁻¹
  rw [Real.sqrt_prod _ (fun i _ => (hQ.eigenvalues_pos i).le)]

theorem cavity_gaussian_precision_integrable {d : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosDef)
    (l : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      Real.exp ((‖x‖ ^ 2 - ⟪x, Q.toEuclideanLin x⟫) / 2 + ⟪l, x⟫))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  simp_rw [cavity_eigenbasis_exponent Q hQ.1 l]
  exact cavity_gaussian_basis_integrable hQ.1.eigenvectorBasis
    (fun i => 1 - hQ.1.eigenvalues i) (fun i => hQ.1.eigenvectorBasis.repr l i)
    (fun i => by simpa only [sub_sub_cancel] using hQ.eigenvalues_pos i)

/-- Standard-Gaussian square completion with an arbitrary positive definite
precision matrix.  No simultaneous diagonalization with the original
covariance is assumed. -/
theorem cavity_gaussian_precision_integral {d : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosDef)
    (l : EuclideanSpace ℝ (Fin d)) :
    (∫ x : EuclideanSpace ℝ (Fin d),
      Real.exp ((‖x‖ ^ 2 - ⟪x, Q.toEuclideanLin x⟫) / 2 + ⟪l, x⟫)
      ∂stdGaussian (EuclideanSpace ℝ (Fin d))) =
      (Real.sqrt Q.det)⁻¹ * Real.exp (⟪l, Q⁻¹.toEuclideanLin l⟫ / 2) := by
  simp_rw [cavity_eigenbasis_exponent Q hQ.1 l]
  have hp : ∀ i, 0 < 1 - (1 - hQ.1.eigenvalues i) := by
    intro i
    simpa only [sub_sub_cancel] using hQ.eigenvalues_pos i
  rw [cavity_gaussian_basis_integral hQ.1.eigenvectorBasis
    (fun i => 1 - hQ.1.eigenvalues i) (fun i => hQ.1.eigenvectorBasis.repr l i) hp]
  simp only [sub_sub_cancel]
  rw [cavity_precision_normalizer Q hQ, cavity_eigenbasis_inverse_quadratic Q hQ,
    Finset.sum_div]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  ring

end InvariantIsing

end

end OAI
