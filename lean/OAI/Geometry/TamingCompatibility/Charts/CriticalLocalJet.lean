import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.CriticalRescale

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution Filter LineDeriv Set
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma schwartz_derivative_eventuallyEq {f g : 𝓢(E,F)} {x : E}
    (h : (f : E → F) =ᶠ[𝓝 x] g) (v : E) :
    ((∂_{v} f : 𝓢(E,F)) : E → F) =ᶠ[𝓝 x] ((∂_{v} g : 𝓢(E,F)) : E → F) := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  exact congrArg (fun t : E →L[ℝ] F => t v) hy

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma rescale_cutoff_two_jet (χ : 𝓢(E,ℂ)) (p : E) {r : ℝ} (hr : 0 < r)
    (u : 𝓢(E,F)) (x : E) (hχ : (χ : E → ℂ) =ᶠ[𝓝 x] fun _ => 1) :
    let w := SchwartzMap.smulLeftCLM F χ (rescaleSchwartz p r hr.ne' u)
    ‖w x‖ + ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} w) x‖ +
      ∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ E j} (∂_{stdOrthonormalBasis ℝ E i} w)) x‖ =
    ‖u (r • x+p)‖ + r * ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} u) (r • x+p)‖ +
      r^2 * ∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ E j} (∂_{stdOrthonormalBasis ℝ E i} u)) (r • x+p)‖ := by
  dsimp only
  have he : (SchwartzMap.smulLeftCLM F χ (rescaleSchwartz p r hr.ne' u) : E → F) =ᶠ[𝓝 x]
      (rescaleSchwartz p r hr.ne' u : E → F) := by
    filter_upwards [hχ] with y hy
    simp [χ.hasTemperateGrowth,hy]
  have h0 := he.self_of_nhds
  have h1 (v : E) := (schwartz_derivative_eventuallyEq he v).self_of_nhds
  have h2 (v w : E) := (schwartz_derivative_eventuallyEq (schwartz_derivative_eventuallyEq he v) w).self_of_nhds
  simp only [h0,h1,h2,rescaleSchwartz_derivative,lineDerivOp_smul,smul_apply,norm_smul,
    Real.norm_eq_abs,abs_of_pos hr,rescaleSchwartz_apply]
  simp only [← Finset.mul_sum]
  ring

end TamingCompatibility.HilbertSobolev

end

end OAI
