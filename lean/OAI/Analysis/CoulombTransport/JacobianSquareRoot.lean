import Mathlib

namespace OAI

universe uIndex uE uD

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise

namespace Problem356.JacobianSquareRoot

/-- The determinant is a smooth polynomial in the matrix entries. -/
theorem contDiff_matrix_det {ι : Type uIndex} [Fintype ι] [DecidableEq ι]
    (n : WithTop ENat) : ContDiff ℝ n (Matrix.det : Matrix ι ι ℝ → ℝ) := by
  classical
  change ContDiff ℝ n (fun M : Matrix ι ι ℝ => M.det)
  simp only [Matrix.det_apply']
  apply ContDiff.sum
  intro σ hσ
  apply contDiff_const.mul
  apply contDiff_prod
  intro i hi
  exact contDiff_apply_apply ℝ ℝ (σ i) i

/-- The determinant is smooth on continuous linear endomorphisms in finite dimension. -/
theorem contDiff_clm_det {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (n : WithTop ENat) :
    ContDiff ℝ n (fun A : E →L[ℝ] E => A.det) := by
  let b := Module.finBasis ℝ E
  have hM : ContDiff ℝ n (fun A : E →L[ℝ] E =>
      LinearMap.toMatrix b b (A : E →ₗ[ℝ] E)) :=
    (((LinearMap.toMatrix b b).toLinearMap.comp
      (ContinuousLinearMap.coeLM ℝ)).toContinuousLinearMap).contDiff
  simpa only [Function.comp_def, LinearMap.det_toMatrix] using
    (contDiff_matrix_det n).comp hM

/-- Nonzero determinants yield smooth absolute-Jacobian square roots. -/
theorem contDiffOn_sqrt_abs_det
    {D : Type uD} {E : Type uE} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : WithTop ENat} {U : Set D} {A : D → E →L[ℝ] E}
    (hA : ContDiffOn ℝ n A U) (hdet : ∀ x ∈ U, (A x).det ≠ 0) :
    ContDiffOn ℝ n (fun x => Real.sqrt |(A x).det|) U := by
  have hd : ContDiffOn ℝ n (fun x => (A x).det) U :=
    (contDiff_clm_det n).fun_comp_contDiffOn hA
  have ha : ContDiffOn ℝ n (fun x => |(A x).det|) U := by
    simpa only [Real.norm_eq_abs] using hd.norm ℝ hdet
  exact ha.sqrt (fun x hx => abs_ne_zero.mpr (hdet x hx))

/-- Invertibility of an endomorphism implies its Jacobian determinant is nonzero. -/
theorem det_ne_zero_of_isInvertible
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : E →L[ℝ] E} (hA : A.IsInvertible) : A.det ≠ 0 := by
  rcases hA with ⟨e, rfl⟩
  exact e.toLinearEquiv.isUnit_det'.ne_zero

/-- Smoothness of the square root of the absolute derivative determinant on an open set. -/
theorem contDiffOn_sqrt_abs_det_fderiv
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U : Set E} {F : E → E} (hU : IsOpen U)
    (hF : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) F U)
    (hdet : ∀ x ∈ U, (fderiv ℝ F x).det ≠ 0) :
    ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat)
      (fun x => Real.sqrt |(fderiv ℝ F x).det|) U := by
  apply contDiffOn_sqrt_abs_det
  · exact ((contDiffOn_infty_iff_fderiv_of_isOpen hU).mp hF).2
  · exact hdet

/-- Multiplication by the composed source amplitude gives the local transported amplitude. -/
theorem contDiffOn_transportedAmplitude
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U : Set E} {F : E → E} {g : E → ℝ} (hU : IsOpen U)
    (hF : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) F U)
    (hg : ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) g)
    (hdet : ∀ x ∈ U, (fderiv ℝ F x).det ≠ 0) :
    ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat)
      (fun x => g (F x) * Real.sqrt |(fderiv ℝ F x).det|) U :=
  (hg.fun_comp_contDiffOn hF).mul (contDiffOn_sqrt_abs_det_fderiv hU hF hdet)

/-- An eventually defined differentiable left inverse forces a nonzero derivative determinant. -/
theorem det_fderiv_ne_zero_of_eventual_leftInverse
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : E → E} {x : E} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G (F x))
    (hGF : ∀ᶠ y in nhds x, G (F y) = y) : (fderiv ℝ F x).det ≠ 0 := by
  have hc : (fderiv ℝ G (F x)).comp (fderiv ℝ F x) =
      ContinuousLinearMap.id ℝ E :=
    (hG.hasFDerivAt.comp x hF.hasFDerivAt).unique
      ((hasFDerivAt_id x).congr_of_eventuallyEq hGF)
  have hprod := congrArg (fun A : E →L[ℝ] E => A.det) hc
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.det_comp, ContinuousLinearMap.coe_id, LinearMap.det_id] at hprod
  change (fderiv ℝ G (F x)).det * (fderiv ℝ F x).det = 1 at hprod
  intro hz
  rw [hz, mul_zero] at hprod
  exact zero_ne_one hprod

/-- Both smooth directions of an open partial homeomorphism have nonvanishing inverse Jacobian. -/
theorem det_fderiv_symm_ne_zero
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) e e.source)
    (he' : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) e.symm e.target)
    {y : E} (hy : y ∈ e.target) : (fderiv ℝ e.symm y).det ≠ 0 := by
  apply det_fderiv_ne_zero_of_eventual_leftInverse
    ((he'.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp))
    ((he.contDiffAt (e.open_source.mem_nhds (e.map_target hy))).differentiableAt (by simp))
  exact e.eventually_right_inverse hy

/-- Smooth inverse-Jacobian factor for a smooth open partial diffeomorphism. -/
theorem contDiffOn_sqrt_abs_det_fderiv_symm
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) e e.source)
    (he' : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) e.symm e.target) :
    ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat)
      (fun y => Real.sqrt |(fderiv ℝ e.symm y).det|) e.target :=
  contDiffOn_sqrt_abs_det_fderiv e.open_target he'
    (fun _ hy => det_fderiv_symm_ne_zero e he he' hy)

/-- Local transported amplitudes are smooth, with no separate Jacobian hypothesis. -/
theorem contDiffOn_transportedAmplitude_symm
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) e e.source)
    (he' : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) e.symm e.target)
    {g : E → ℝ} (hg : ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) g) :
    ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat)
      (fun y => g (e.symm y) * Real.sqrt |(fderiv ℝ e.symm y).det|) e.target :=
  (hg.fun_comp_contDiffOn he').mul (contDiffOn_sqrt_abs_det_fderiv_symm e he he')

/-- The transported amplitude squares to the Jacobian-weighted source density. -/
theorem transportedAmplitude_sq
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) (g : E → ℝ) (y : E) :
    (g (F y) * Real.sqrt |(fderiv ℝ F y).det|) ^ 2 =
      |(fderiv ℝ F y).det| * (g (F y)) ^ 2 := by
  rw [mul_pow, Real.sq_sqrt (abs_nonneg _), mul_comm]

end Problem356.JacobianSquareRoot

end

end OAI
