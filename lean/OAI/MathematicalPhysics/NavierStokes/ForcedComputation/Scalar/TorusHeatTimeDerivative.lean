import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusHeatKernelEquation
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.ScalarMassEvolution

namespace OAI

/-! Time differentiation of the prescribed heat convolution at positive time. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set MeasureTheory Filter
open scoped Topology ContDiff

def heatLaplacianIntegral (g : Plane → ℝ) (t : ℝ) (x : Plane) : ℝ :=
  ∫ y in Icc (0 : Plane) (fun _ => 1), scalarLaplacian (torusHeatKernel t) (x-y) * g y

theorem torusHeatEvolution_log_hasDerivAt {g : Plane → ℝ} (hg : Continuous g)
    (s : ℝ) (x : Plane) :
    HasDerivAt (fun r => torusHeatEvolution g (Real.exp r) x)
      (Real.exp s * heatLaplacianIntegral g (Real.exp s) x) s := by
  let W : ℝ → Plane → ℝ := fun r y => torusHeatKernel (Real.exp r) (x-y) * g y
  let D : ℝ → Plane → ℝ := fun r y =>
    Real.exp r * (scalarLaplacian (torusHeatKernel (Real.exp r)) (x-y) * g y)
  have hi : ContDiff ℝ ∞ (fun p : ℝ × Plane => (p.1, x-p.2)) :=
    contDiff_fst.prodMk (contDiff_const.sub contDiff_snd)
  have hW : Continuous (Function.uncurry W) :=
    (torusHeatKernel_exp_smooth.comp hi).continuous.mul (hg.comp continuous_snd)
  have hD : Continuous (Function.uncurry D) :=
    (Real.continuous_exp.comp continuous_fst).mul
      ((torusHeatKernel_laplacian_exp_smooth.comp hi).continuous.mul
        (hg.comp continuous_snd))
  have hd (r : ℝ) (y : Plane) : HasDerivAt (fun u => W u y) (D r y) r := by
    have h := ((torusHeatKernel_equation (Real.exp_pos r) (x-y)).comp r
      (Real.hasDerivAt_exp r)).mul_const (g y)
    change HasDerivAt (fun u => W u y) _ r at h
    convert! h using 1
    dsimp [D]
    ring
  have h := scalarMass_hasDerivAt hW hD hd s
  have he : (fun r => torusHeatEvolution g (Real.exp r) x) = scalarMass W := by
    funext r
    rw [torusHeatEvolution, ite_eq_right (not_le.mpr (Real.exp_pos r))]
    rfl
  rw [he]
  convert h using 1
  dsimp [scalarMass, D, heatLaplacianIntegral]
  rw [integral_const_mul]

theorem torusHeatEvolution_hasDerivAt {g : Plane → ℝ} (hg : Continuous g)
    {t : ℝ} (ht : 0 < t) (x : Plane) :
    HasDerivAt (fun s => torusHeatEvolution g s x) (heatLaplacianIntegral g t x) t := by
  have h := (torusHeatEvolution_log_hasDerivAt hg (Real.log t) x).comp t
    (Real.hasDerivAt_log ht.ne')
  have he : (Real.exp (Real.log t) * heatLaplacianIntegral g (Real.exp (Real.log t)) x) *
      t⁻¹ = heatLaplacianIntegral g t x := by
    rw [Real.exp_log ht]
    field_simp
  rw [he] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  simp only [Function.comp_def, Real.exp_log hs]

end ForcedComputation.VelocityDetector

end

end OAI
