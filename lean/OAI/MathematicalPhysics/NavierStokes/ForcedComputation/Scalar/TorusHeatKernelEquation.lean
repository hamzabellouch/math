import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusHeatPositiveSmooth

namespace OAI

/-! The Gaussian lattice kernel satisfies the coordinate heat equation.
Fourier products keep the two first and second spatial derivatives explicit. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows PlanarHamiltonian Set
open scoped ContDiff

def torusHeatFourierProduct (c : ℂ) (k l : ℕ) (t : ℝ) (x : Plane) : ℝ :=
  (c * periodicHeatMoment k (t, x 0) * periodicHeatMoment l (t, x 1)).re

theorem torusHeatFourierProduct_time (c : ℂ) (k l : ℕ) {t : ℝ}
    (ht : 0 < t) (x : Plane) :
    HasDerivAt (fun s => torusHeatFourierProduct c k l s x)
      (torusHeatFourierProduct (-4 * (Real.pi : ℂ)^2 * c) (k+2) l t x +
        torusHeatFourierProduct (-4 * (Real.pi : ℂ)^2 * c) k (l+2) t x) t := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    (((periodicHeatMoment_time k ht (x 0)).const_mul c).mul
      (periodicHeatMoment_time l ht (x 1)))
  change HasDerivAt (fun s => torusHeatFourierProduct c k l s x) _ t at h
  convert! h using 1
  simp only [torusHeatFourierProduct, Complex.reCLM_apply]
  rw [← Complex.add_re]
  congr 1
  ring

private theorem moment_plane_deriv (k : ℕ) {t : ℝ} (ht : 0 < t)
    (x : Plane) (j : Fin 2) :
    HasFDerivAt (fun y : Plane => periodicHeatMoment k (t, y j))
      ((ContinuousLinearMap.proj j : Plane →L[ℝ] ℝ).smulRight
        (2 * (Real.pi : ℂ) * Complex.I * periodicHeatMoment (k+1) (t, x j))) x := by
  have h := periodicHeatMoment_space k ht (x j)
  change HasDerivAt (fun y => periodicHeatMoment k (t, y)) _
    ((ContinuousLinearMap.proj j : Plane →L[ℝ] ℝ) x) at h
  convert! h.hasFDerivAt.comp x
    (ContinuousLinearMap.proj j : Plane →L[ℝ] ℝ).hasFDerivAt using 1

theorem torusHeatFourierProduct_spatialD_zero (c : ℂ) (k l : ℕ) {t : ℝ}
    (ht : 0 < t) :
    spatialD 0 (torusHeatFourierProduct c k l t) =
      torusHeatFourierProduct (c * (2 * (Real.pi : ℂ) * Complex.I)) (k+1) l t := by
  funext x
  have h := Complex.reCLM.hasFDerivAt.comp x
    (((moment_plane_deriv k ht x 0).const_mul c).mul (moment_plane_deriv l ht x 1))
  change HasFDerivAt (torusHeatFourierProduct c k l t) _ x at h
  rw [spatialD, h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, add_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply,
    ContinuousLinearMap.proj_apply, PlanarHamiltonian.basis, Pi.single_eq_same, Pi.single_eq_of_ne
      (show (1 : Fin 2) ≠ 0 by decide), zero_smul, one_smul,
    Complex.reCLM_apply, torusHeatFourierProduct]
  congr 1
  ring

theorem torusHeatFourierProduct_spatialD_one (c : ℂ) (k l : ℕ) {t : ℝ}
    (ht : 0 < t) :
    spatialD 1 (torusHeatFourierProduct c k l t) =
      torusHeatFourierProduct (c * (2 * (Real.pi : ℂ) * Complex.I)) k (l+1) t := by
  funext x
  have h := Complex.reCLM.hasFDerivAt.comp x
    (((moment_plane_deriv k ht x 0).const_mul c).mul (moment_plane_deriv l ht x 1))
  change HasFDerivAt (torusHeatFourierProduct c k l t) _ x at h
  rw [spatialD, h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, add_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply,
    ContinuousLinearMap.proj_apply, PlanarHamiltonian.basis, Pi.single_eq_same, Pi.single_eq_of_ne
      (show (0 : Fin 2) ≠ 1 by decide), zero_smul, one_smul,
    Complex.reCLM_apply, torusHeatFourierProduct]
  congr 1
  ring

theorem torusHeatKernel_eq_fourierProduct {t : ℝ} (ht : 0 < t) :
    torusHeatKernel t = torusHeatFourierProduct 1 0 0 t := by
  funext x
  simpa only [torusHeatFourierProduct, one_mul, Complex.ofReal_re] using
    congrArg Complex.re (torusHeatKernel_complex ht x)

theorem torusHeatKernel_laplacian {t : ℝ} (ht : 0 < t) (x : Plane) :
    scalarLaplacian (torusHeatKernel t) x =
      torusHeatFourierProduct (-4 * (Real.pi : ℂ)^2) 2 0 t x +
        torusHeatFourierProduct (-4 * (Real.pi : ℂ)^2) 0 2 t x := by
  have hc : (1 : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) *
      (2 * (Real.pi : ℂ) * Complex.I) = -4 * (Real.pi : ℂ)^2 := by
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [torusHeatKernel_eq_fourierProduct ht]
  simp only [scalarLaplacian, Fin.sum_univ_two,
    torusHeatFourierProduct_spatialD_zero _ _ _ ht,
    torusHeatFourierProduct_spatialD_one _ _ _ ht, hc]

theorem torusHeatFourierProduct_exp_smooth (c : ℂ) (k l : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × Plane => torusHeatFourierProduct c k l (Real.exp p.1) p.2) := by
  have hm (m : ℕ) (j : Fin 2) : ContDiff ℝ ∞
      (fun p : ℝ × Plane => periodicHeatMoment m (Real.exp p.1, p.2 j)) := by
    have h := (periodicHeatMoment_smooth m).comp
      (contDiff_fst.exp.prodMk ((contDiff_apply ℝ ℝ j).comp contDiff_snd)).contDiffOn
      (show MapsTo (fun p : ℝ × Plane => (Real.exp p.1, p.2 j)) univ
        (Ioi (0 : ℝ) ×ˢ univ) from fun _ _ => ⟨Real.exp_pos _, mem_univ _⟩)
    simpa only [Function.comp_def, contDiffOn_univ] using h
  exact Complex.reCLM.contDiff.comp ((contDiff_const.mul (hm k 0)).mul (hm l 1))

theorem torusHeatKernel_laplacian_exp_smooth :
    ContDiff ℝ ∞ (fun p : ℝ × Plane => scalarLaplacian (torusHeatKernel (Real.exp p.1)) p.2) := by
  have h := (torusHeatFourierProduct_exp_smooth (-4 * (Real.pi : ℂ)^2) 2 0).add
    (torusHeatFourierProduct_exp_smooth (-4 * (Real.pi : ℂ)^2) 0 2)
  convert h using 1
  funext p
  exact torusHeatKernel_laplacian (Real.exp_pos _) _

theorem torusHeatKernel_equation {t : ℝ} (ht : 0 < t) (x : Plane) :
    HasDerivAt (fun s => torusHeatKernel s x)
      (scalarLaplacian (torusHeatKernel t) x) t := by
  have h := torusHeatFourierProduct_time 1 0 0 ht x
  rw [torusHeatKernel_laplacian ht]
  simp only [mul_one] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact congrFun (torusHeatKernel_eq_fourierProduct hs) x

end ForcedComputation.VelocityDetector

end

end OAI
