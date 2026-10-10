import OAI.Probability.InvariantIsing.Cavity.CavityScalarResolventBound
import OAI.Probability.InvariantIsing.Cavity.CavityGaussianSpectral

namespace OAI

/-! The smooth resolvent path of a compressed finite-alphabet matrix.
Its norm bounds depend on the alphabet mass, not on the number of cascade levels. -/

noncomputable section
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator MatrixOrder

namespace InvariantIsing

variable {ι : Type*} [Fintype ι] {d : ℕ}

def cavitySpectralMatrixPath (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian)
    (x : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
    (Matrix.diagonal (fun i => cavityScalarResolvent ρ eig hρ hρsum (hA.eigenvalues i) x))

def cavitySpectralMatrixDensity (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian)
    (x : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
    (Matrix.diagonal (fun i => 1 /
      (finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) *
        (finiteInverse ρ eig hρ hρsum x - hA.eigenvalues i)^2)))

private lemma cavity_conjugate_diagonal_norm {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.IsHermitian) (f : Fin d → ℝ) :
    ‖Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary (Matrix.diagonal f)‖ = ‖f‖ := by
  simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]

lemma cavitySpectralMatrixPath_zero (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian) :
    cavitySpectralMatrixPath ρ eig hρ hρsum A hA 0 = 0 := by
  simp [cavitySpectralMatrixPath, cavityScalarResolvent]

theorem cavitySpectralMatrixPath_lipschitz (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian)
    (a : ι) (heig : ∀ i, hA.eigenvalues i ≤ eig a)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    ‖cavitySpectralMatrixPath ρ eig hρ hρsum A hA y -
      cavitySpectralMatrixPath ρ eig hρ hρsum A hA x‖ ≤ (ρ a)⁻¹ * (y - x) := by
  rw [cavitySpectralMatrixPath, cavitySpectralMatrixPath, ← map_sub, Matrix.diagonal_sub,
    cavity_conjugate_diagonal_norm]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (inv_nonneg.mpr (hρ a).le)
    (sub_nonneg.mpr hxy))).mpr
  intro i
  exact cavityScalarResolvent_lipschitz ρ eig hρ hρsum a (heig i) hx hxy

theorem cavitySpectralMatrixDensity_norm_le (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian)
    (a : ι) (heig : ∀ i, hA.eigenvalues i ≤ eig a) {x : ℝ} (hx : 0 < x) :
    ‖cavitySpectralMatrixDensity ρ eig hρ hρsum A hA x‖ ≤ (ρ a)⁻¹ := by
  rw [cavitySpectralMatrixDensity, cavity_conjugate_diagonal_norm]
  apply (pi_norm_le_iff_of_nonneg (inv_nonneg.mpr (hρ a).le)).mpr
  intro i
  have h := cavityScalarResolvent_derivative_bound ρ eig hρ hρsum a (heig i) hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

theorem hasDerivAt_cavitySpectralMatrixPath (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian)
    (a : ι) (heig : ∀ i, hA.eigenvalues i ≤ eig a) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (cavitySpectralMatrixPath ρ eig hρ hρsum A hA)
      (cavitySpectralMatrixDensity ρ eig hρ hρsum A hA x) x := by
  let diag : (Fin d → ℝ) →L[ℝ] Matrix (Fin d) (Fin d) ℝ :=
    ({ toFun := Matrix.diagonal
       map_add' := fun f g => (Matrix.diagonal_add f g).symm
       map_smul' := fun c f => Matrix.diagonal_smul c f } :
      (Fin d → ℝ) →ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ).toContinuousLinearMap
  have hc := hasDerivAt_pi.mpr (fun i =>
    hasDerivAt_cavityScalarResolvent ρ eig hρ hρsum a (heig i) hx)
  have hd := diag.hasFDerivAt.comp_hasDerivAt x hc
  have hm := (hd.const_mul (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)).mul_const
    (star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ))
  convert! hm using 1

theorem cavitySpectralMatrixPath_pos_eq (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian)
    (a : ι) (heig : ∀ i, hA.eigenvalues i ≤ eig a) {x : ℝ} (hx : 0 < x) :
    cavitySpectralMatrixPath ρ eig hρ hρsum A hA x =
      (finiteInverse ρ eig hρ hρsum x • (1 : Matrix (Fin d) (Fin d) ℝ) - A)⁻¹ := by
  let U := Unitary.conjStarAlgAut ℝ (Matrix (Fin d) (Fin d) ℝ) hA.eigenvectorUnitary
  let b := finiteInverse ρ eig hρ hρsum x
  have hb : ∀ i, b - hA.eigenvalues i ≠ 0 := fun i =>
    (sub_pos.mpr ((heig i).trans_lt ((finiteInverse_spec ρ eig hρ hρsum hx).1 a))).ne'
  have hdiag : b • (1 : Matrix (Fin d) (Fin d) ℝ) - A =
      U (Matrix.diagonal (fun i => b - hA.eigenvalues i)) := by
    have ha : U (Matrix.diagonal hA.eigenvalues) = A := by
      simpa [U] using hA.spectral_theorem.symm
    have hc : (Matrix.diagonal fun _ : Fin d => b) = b • (1 : Matrix (Fin d) (Fin d) ℝ) := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    rw [← Matrix.diagonal_sub, hc, map_sub, map_smul, map_one, ha]
  have he : cavitySpectralMatrixPath ρ eig hρ hρsum A hA x =
      U (Matrix.diagonal (fun i => (b - hA.eigenvalues i)⁻¹)) := by
    simp only [cavitySpectralMatrixPath, cavityScalarResolvent_pos_eq ρ eig hρ hρsum a,
      heig, hx, U, b]
  rw [he]
  symm
  apply Matrix.inv_eq_right_inv
  rw [hdiag, ← map_mul, Matrix.diagonal_mul_diagonal]
  simp [hb]

end InvariantIsing

end

end OAI
