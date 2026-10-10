import OAI.Probability.InvariantIsing.Cavity.CavityMatrixResolventBound
import OAI.Probability.InvariantIsing.Cavity.CavityResolventDerivative

namespace OAI

/-! The actual quadratic change from the base spectral matrix to the full
spectral matrix, including the derivative which transports the common root. -/

noncomputable section
open Filter
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

variable {ι : Type*} [Fintype ι] {d : ℕ}

lemma cavitySpectralMatrixDensity_posSemidef (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hsum : ∑ a, ρ a = 1) (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian)
    (a : ι) (heig : ∀ i, hA.eigenvalues i ≤ eig a) {x : ℝ} (hx : 0 < x) :
    (cavitySpectralMatrixDensity ρ eig hρ hsum A hA x).PosSemidef := by
  have hp : (Matrix.diagonal (fun i : Fin d => 1 /
      (finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hsum x) *
        (finiteInverse ρ eig hρ hsum x - hA.eigenvalues i)^2))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i =>
      (cavityScalarResolvent_derivative_bound ρ eig hρ hsum a (heig i) hx).1)
  simpa only [cavitySpectralMatrixDensity, Unitary.conjStarAlgAut_apply,
    Matrix.star_eq_conjTranspose] using
      hp.mul_mul_conjTranspose_same (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)

lemma cavity_spectral_shift_isUnit (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hsum : ∑ a, ρ a = 1) (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian)
    (a : ι) (heig : ∀ i, hA.eigenvalues i ≤ eig a) {x : ℝ} (hx : 0 < x) :
    IsUnit (finiteInverse ρ eig hρ hsum x • (1 : Matrix (Fin d) (Fin d) ℝ) - A).det := by
  let U := Unitary.conjStarAlgAut ℝ (Matrix (Fin d) (Fin d) ℝ) hA.eigenvectorUnitary
  let b := finiteInverse ρ eig hρ hsum x
  have ha : U (Matrix.diagonal hA.eigenvalues) = A := by
    simpa [U] using hA.spectral_theorem.symm
  have hc : (Matrix.diagonal fun _ : Fin d => b) = b • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hd : b • (1 : Matrix (Fin d) (Fin d) ℝ) - A =
      U (Matrix.diagonal (fun i => b - hA.eigenvalues i)) := by
    rw [← Matrix.diagonal_sub, hc, map_sub, map_smul, map_one, ha]
  have hp := Matrix.PosDef.diagonal (fun i =>
    sub_pos.mpr ((heig i).trans_lt ((finiteInverse_spec ρ eig hρ hsum hx).1 a)))
  have hu : IsUnit (Matrix.diagonal (fun i => b - hA.eigenvalues i)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hp.det_pos.ne')
  change IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).det
  rw [hd]
  exact (Matrix.isUnit_iff_isUnit_det _).mp (hu.map U.toRingHom)

theorem cavity_spectral_transform (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hsum : ∑ a, ρ a = 1) (A A₀ : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.IsHermitian) (hA₀ : A₀.IsHermitian)
    (a : ι) (heig : ∀ i, hA.eigenvalues i ≤ eig a)
    (heig₀ : ∀ i, hA₀.eigenvalues i ≤ eig a) {x : ℝ} (hx : 0 < x) :
    cavityResolvent (A - A₀) (cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ x) =
      cavitySpectralMatrixPath ρ eig hρ hsum A hA x := by
  rw [cavitySpectralMatrixPath_pos_eq ρ eig hρ hsum A₀ hA₀ a heig₀ hx,
    cavitySpectralMatrixPath_pos_eq ρ eig hρ hsum A hA a heig hx]
  exact cavityResolvent_spectral_transform A A₀ _
    (cavity_spectral_shift_isUnit ρ eig hρ hsum A₀ hA₀ a heig₀ hx)
    (cavity_spectral_shift_isUnit ρ eig hρ hsum A hA a heig hx)

lemma cavity_spectral_tilt_isUnit (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hsum : ∑ a, ρ a = 1) (A A₀ : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.IsHermitian) (hA₀ : A₀.IsHermitian)
    (a : ι) (heig : ∀ i, hA.eigenvalues i ≤ eig a)
    (heig₀ : ∀ i, hA₀.eigenvalues i ≤ eig a) {x : ℝ} (hx : 0 < x) :
    IsUnit (1 - cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ x * (A - A₀)).det := by
  let b := finiteInverse ρ eig hρ hsum x
  let D₀ := b • (1 : Matrix (Fin d) (Fin d) ℝ) - A₀
  let D := b • (1 : Matrix (Fin d) (Fin d) ℝ) - A
  have h₀ : IsUnit D₀.det := cavity_spectral_shift_isUnit ρ eig hρ hsum A₀ hA₀ a heig₀ hx
  have h : IsUnit D.det := cavity_spectral_shift_isUnit ρ eig hρ hsum A hA a heig hx
  rw [cavitySpectralMatrixPath_pos_eq ρ eig hρ hsum A₀ hA₀ a heig₀ hx]
  change IsUnit (1 - D₀⁻¹ * (A - A₀)).det
  have he : 1 - D₀⁻¹ * (A - A₀) = D₀⁻¹ * D := by
    calc
      _ = D₀⁻¹ * D₀ - D₀⁻¹ * (A - A₀) := by rw [Matrix.nonsing_inv_mul _ h₀]
      _ = _ := by dsimp only [D, D₀]; noncomm_ring
  rw [he, Matrix.det_mul]
  exact (Matrix.isUnit_nonsing_inv_det_iff.mpr h₀).mul h

theorem cavity_spectral_root_transform (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hsum : ∑ a, ρ a = 1) (A A₀ : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.IsHermitian) (hA₀ : A₀.IsHermitian)
    (a : ι) (heig : ∀ i, hA.eigenvalues i ≤ eig a)
    (heig₀ : ∀ i, hA₀.eigenvalues i ≤ eig a) {x : ℝ} (hx : 0 < x) :
    let H := cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀
    (1 - H x * (A - A₀))⁻¹ * cavitySpectralMatrixDensity ρ eig hρ hsum A₀ hA₀ x *
      ((1 - H x * (A - A₀))⁻¹).transpose =
        cavitySpectralMatrixDensity ρ eig hρ hsum A hA x := by
  intro H
  have hK : (A - A₀).transpose = A - A₀ := by
    rw [Matrix.transpose_sub, Matrix.isHermitian_iff_isSymm.mp hA,
      Matrix.isHermitian_iff_isSymm.mp hA₀]
  have hH : (H x).transpose = H x := by
    dsimp only [H]
    rw [cavitySpectralMatrixPath_pos_eq ρ eig hρ hsum A₀ hA₀ a heig₀ hx,
      Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_one, Matrix.isHermitian_iff_isSymm.mp hA₀]
  have hd := hasDerivAt_cavityResolvent (A - A₀) H
    (cavitySpectralMatrixDensity ρ eig hρ hsum A₀ hA₀ x) x hK hH
    (hasDerivAt_cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ a heig₀ hx)
    (cavity_spectral_tilt_isUnit ρ eig hρ hsum A A₀ hA hA₀ a heig heig₀ hx)
  have he : (fun t => cavityResolvent (A - A₀) (H t)) =ᶠ[𝓝 x]
      cavitySpectralMatrixPath ρ eig hρ hsum A hA := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    exact cavity_spectral_transform ρ eig hρ hsum A A₀ hA hA₀ a heig heig₀ ht
  exact (hd.congr_of_eventuallyEq he.symm).unique
    (hasDerivAt_cavitySpectralMatrixPath ρ eig hρ hsum A hA a heig hx)

end InvariantIsing

end

end OAI
