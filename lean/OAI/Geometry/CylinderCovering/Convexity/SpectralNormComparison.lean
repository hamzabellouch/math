import OAI.Geometry.CylinderCovering.Convexity.SpectralNormComparisonDefinitions
import OAI.Geometry.RuledCovering.Model

namespace OAI

noncomputable section
open Module
namespace SpectralNormComparison

@[simp] theorem offDiagonal_apply (a b : ℝ) (x : Plane) :
    offDiagonal a b x = !₂[a * x 1, b * x 0] := rfl

@[simp] theorem offDiagonalLinear_apply (a b : ℝ) (x : Plane) :
    offDiagonalLinear a b x = !₂[a * x 1, b * x 0] := rfl

theorem norm_sq (x : Plane) : ‖x‖ ^ 2 = (x 0)^2 + (x 1)^2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

theorem norm_offDiagonal (a b : ℝ) : ‖offDiagonal a b‖ = max |a| |b| := by
  apply le_antisymm
  · apply (offDiagonal a b).opNorm_le_bound (le_trans (abs_nonneg a) (le_max_left _ _))
    intro x
    have ha : a^2 ≤ (max |a| |b|)^2 := by
      simpa only [sq_abs] using sq_le_sq₀ (abs_nonneg a)
        (le_trans (abs_nonneg a) (le_max_left |a| |b|)) |>.mpr (le_max_left |a| |b|)
    have hb : b^2 ≤ (max |a| |b|)^2 := by
      simpa only [sq_abs] using sq_le_sq₀ (abs_nonneg b)
        (le_trans (abs_nonneg b) (le_max_right |a| |b|)) |>.mpr (le_max_right |a| |b|)
    have h1 := mul_le_mul_of_nonneg_right ha (sq_nonneg (x 1))
    have h2 := mul_le_mul_of_nonneg_right hb (sq_nonneg (x 0))
    have hs : ‖offDiagonal a b x‖^2 ≤ (max |a| |b| * ‖x‖)^2 := by
      rw [mul_pow, norm_sq, norm_sq]
      simp only [offDiagonal_apply, WithLp.ofLp_toLp, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      nlinarith
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
      (le_trans (abs_nonneg a) (le_max_left _ _)) (norm_nonneg _))).mp hs
  · apply max_le
    · have h := (offDiagonal a b).le_opNorm (!₂[0, 1] : Plane)
      simpa [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_sq_eq_abs] using h
    · have h := (offDiagonal a b).le_opNorm (!₂[1, 0] : Plane)
      simpa [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_sq_eq_abs] using h

theorem hasEigenvalue_conj
    {E F : Type*} [AddCommGroup E] [AddCommGroup F]
    [Module ℝ E] [Module ℝ F] (e : E ≃ₗ[ℝ] F)
    {A : E →ₗ[ℝ] E} {mu : ℝ} (hA : Module.End.HasEigenvalue A mu) :
    Module.End.HasEigenvalue (e.conj A) mu := by
  obtain ⟨x, hx⟩ := hA.exists_hasEigenvector
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := e x)
  constructor
  · rw [Module.End.mem_eigenspace_iff]
    simpa only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply,
      map_smul] using congrArg e hx.apply_eq_smul
  · exact fun h => hx.2 (e.map_eq_zero_iff.mp h)

theorem hasEigenvalue_conj_iff
    {E F : Type*} [AddCommGroup E] [AddCommGroup F]
    [Module ℝ E] [Module ℝ F] (e : E ≃ₗ[ℝ] F)
    (A : E →ₗ[ℝ] E) (mu : ℝ) :
    Module.End.HasEigenvalue (e.conj A) mu ↔ Module.End.HasEigenvalue A mu := by
  constructor
  · intro h
    simpa only [LinearEquiv.conj_symm_conj] using hasEigenvalue_conj e.symm h
  · exact hasEigenvalue_conj e

theorem square_zero_conj_iff
    {E F : Type*} [AddCommGroup E] [AddCommGroup F]
    [Module ℝ E] [Module ℝ F] (e : E ≃ₗ[ℝ] F) (A : E →ₗ[ℝ] E) :
    (e.conj A).comp (e.conj A) = 0 ↔ A.comp A = 0 := by
  rw [← e.conj_comp, e.conj.map_eq_zero_iff]

theorem physicalScale_conj_offDiagonal (h : ℝ) (hh : h ≠ 0) (a b : ℝ) :
    (physicalScale h hh).conj (offDiagonalLinear a b) =
      offDiagonalLinear (a / h) (h * b) := by
  ext x i
  fin_cases i <;> simp [LinearEquiv.conj_apply_apply, physicalScale,
    offDiagonalLinear] <;> ring

theorem comparison_eigenvalues :
    Module.End.HasEigenvalue (offDiagonalLinear 2 (1 / 8)) (1 / 2) ∧
    Module.End.HasEigenvalue (offDiagonalLinear 2 (1 / 8)) (-(1 / 2)) := by
  constructor
  · apply Module.End.hasEigenvalue_of_hasEigenvector (x := (!₂[4, 1] : Plane))
    constructor
    · rw [Module.End.mem_eigenspace_iff]
      ext i
      fin_cases i <;> norm_num [offDiagonalLinear]
    · intro h
      have := congrArg (fun x : Plane => x 0) h
      norm_num at this
  · apply Module.End.hasEigenvalue_of_hasEigenvector (x := (!₂[-4, 1] : Plane))
    constructor
    · rw [Module.End.mem_eigenspace_iff]
      ext i
      fin_cases i <;> norm_num [offDiagonalLinear]
    · intro h
      have := congrArg (fun x : Plane => x 0) h
      norm_num at this

theorem comparison_norm : ‖offDiagonal 2 (1 / 8)‖ = 2 := by
  rw [norm_offDiagonal]
  norm_num

theorem comparison_rescaled_norm :
    ‖LinearMap.toContinuousLinearMap ((physicalScale 4 (by norm_num)).conj
      (offDiagonalLinear 2 (1 / 8)))‖ = 1 / 2 := by
  rw [physicalScale_conj_offDiagonal]
  change ‖offDiagonal (2 / 4) (4 * (1 / 8))‖ = 1 / 2
  rw [norm_offDiagonal]
  norm_num

theorem offDiagonal_square (a b : ℝ) :
    (offDiagonalLinear a b).comp (offDiagonalLinear a b) =
      (a * b) • LinearMap.id := by
  ext x i
  fin_cases i <;> simp [offDiagonalLinear] <;> ring

theorem eigenvalue_sq {a b mu : ℝ}
    (h : Module.End.HasEigenvalue (offDiagonalLinear a b) mu) : mu^2 = a*b := by
  obtain ⟨x, hx⟩ := h.exists_hasEigenvector
  have he := hx.apply_eq_smul
  have hee : mu^2 • x = (a*b) • x := by
    calc
      mu^2 • x = offDiagonalLinear a b (offDiagonalLinear a b x) := by
        rw [he, map_smul, he, smul_smul, pow_two]
      _ = (a*b) • x := congrArg (fun f : Plane →ₗ[ℝ] Plane => f x)
        (offDiagonal_square a b)
  have hz : (mu^2 - a*b) • x = 0 := by rw [sub_smul, hee, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hx.2)

theorem comparison_spectrum (mu : ℝ) :
    Module.End.HasEigenvalue (offDiagonalLinear 2 (1 / 8)) mu ↔
      mu = 1 / 2 ∨ mu = -(1 / 2) := by
  constructor
  · intro h
    have hs := eigenvalue_sq h
    have hz : (mu - 1/2)*(mu + 1/2) = 0 := by nlinarith
    rcases mul_eq_zero.mp hz with hleft | hright
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl)
    · exact comparison_eigenvalues.1
    · exact comparison_eigenvalues.2

theorem comparison_hyperbolic (p : Plane) :
    RuledApproximation.HyperbolicAt 1 (offDiagonal 2 (1/8)) p := by
  refine ⟨1/2, by norm_num, by norm_num, ?_, ?_⟩
  · rw [ContinuousLinearMap.fderiv]
    exact comparison_eigenvalues.1
  · rw [ContinuousLinearMap.fderiv]
    exact comparison_eigenvalues.2

theorem comparison_not_orthogonal_bound (p : Plane) {kappa : ℝ} (hk : kappa < 1) :
    ¬ ‖fderiv ℝ (offDiagonal 2 (1/8)) p‖ ≤ kappa := by
  rw [ContinuousLinearMap.fderiv, comparison_norm]
  linarith

theorem fderiv_physical_conjugate (h : ℝ) (hh : h ≠ 0)
    (v : Plane → Plane) (p : Plane)
    (hv : DifferentiableAt ℝ v ((physicalScale h hh).symm p)) :
    (fderiv ℝ (fun x => physicalScale h hh
      (v ((physicalScale h hh).symm x))) p).toLinearMap =
      (physicalScale h hh).conj
        (fderiv ℝ v ((physicalScale h hh).symm p)).toLinearMap := by
  let e : Plane ≃ₗ[ℝ] Plane := physicalScale h hh
  let eL : Plane →L[ℝ] Plane := LinearMap.toContinuousLinearMap e.toLinearMap
  let eiL : Plane →L[ℝ] Plane := LinearMap.toContinuousLinearMap e.symm.toLinearMap
  have hd := eL.hasFDerivAt.comp p (hv.hasFDerivAt.comp p eiL.hasFDerivAt)
  have he := hd.fderiv
  apply LinearMap.ext
  intro x
  exact congrArg (fun A : Plane →L[ℝ] Plane => A x) he

theorem physical_square_zero_iff (h : ℝ) (hh : h ≠ 0)
    (v : Plane → Plane) (p : Plane)
    (hv : DifferentiableAt ℝ v ((physicalScale h hh).symm p)) :
    let A := (fderiv ℝ (fun x => physicalScale h hh
      (v ((physicalScale h hh).symm x))) p).toLinearMap
    A.comp A = 0 ↔
      (fderiv ℝ v ((physicalScale h hh).symm p)).toLinearMap.comp
        (fderiv ℝ v ((physicalScale h hh).symm p)).toLinearMap = 0 := by
  dsimp only
  rw [fderiv_physical_conjugate h hh v p hv]
  exact square_zero_conj_iff _ _

theorem physical_eigenvalue_iff (h : ℝ) (hh : h ≠ 0)
    (v : Plane → Plane) (p : Plane)
    (hv : DifferentiableAt ℝ v ((physicalScale h hh).symm p)) (mu : ℝ) :
    Module.End.HasEigenvalue
      (fderiv ℝ (fun x => physicalScale h hh
        (v ((physicalScale h hh).symm x))) p).toLinearMap mu ↔
      Module.End.HasEigenvalue
        (fderiv ℝ v ((physicalScale h hh).symm p)).toLinearMap mu := by
  rw [fderiv_physical_conjugate h hh v p hv]
  exact hasEigenvalue_conj_iff _ _ _

end SpectralNormComparison

end

end OAI
