import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PeriodicHeatPoisson
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PeriodicHeatEquation

namespace OAI

/-! Joint smoothness of the explicitly prescribed torus kernel for positive
 time, obtained from its convergent Fourier series. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff

theorem torusHeatKernel_complex {t : ℝ} (ht : 0 < t) (x : Plane) :
    (torusHeatKernel t x : ℂ) =
      periodicHeatMoment 0 (t, x 0) * periodicHeatMoment 0 (t, x 1) := by
  rw [torusHeatKernel_factor ht, periodicHeatMoment_zero_gaussian ht,
    periodicHeatMoment_zero_gaussian ht]
  have hs : (Real.sqrt (4 * Real.pi * t) : ℂ) ^ 2 = (4 * Real.pi * t : ℝ) := by
    exact_mod_cast Real.sq_sqrt (show 0 ≤ 4 * Real.pi * t by positivity)
  calc
    _ = ((Real.sqrt (4 * Real.pi * t) : ℂ) ^ 2)⁻¹ *
        ((gaussianLattice t (x 0) : ℂ) * (gaussianLattice t (x 1) : ℂ)) := by
      rw [hs]
      push_cast
      rfl
    _ = _ := by rw [← inv_pow]; ring

theorem torusHeatKernel_smooth_positive :
    ContDiffOn ℝ ∞ (fun p : ℝ × Plane => torusHeatKernel p.1 p.2)
      (Ioi (0 : ℝ) ×ˢ univ) := by
  have hm (j : Fin 2) : ContDiffOn ℝ ∞
      (fun p : ℝ × Plane => periodicHeatMoment 0 (p.1, p.2 j))
      (Ioi (0 : ℝ) ×ˢ univ) := by
    exact (periodicHeatMoment_smooth 0).comp
      (contDiff_fst.prodMk ((contDiff_apply ℝ ℝ j).comp contDiff_snd)).contDiffOn
      (fun p hp => ⟨hp.1, mem_univ _⟩)
  have h := Complex.reCLM.contDiff.comp_contDiffOn ((hm 0).mul (hm 1))
  apply h.congr
  intro p hp
  exact congrArg Complex.re (torusHeatKernel_complex hp.1 p.2)

theorem torusHeatKernel_exp_smooth :
    ContDiff ℝ ∞ (fun p : ℝ × Plane => torusHeatKernel (Real.exp p.1) p.2) := by
  have h := torusHeatKernel_smooth_positive.comp
    (contDiff_fst.exp.prodMk contDiff_snd).contDiffOn
    (show MapsTo (fun p : ℝ × Plane => (Real.exp p.1, p.2)) univ
      (Ioi (0 : ℝ) ×ˢ univ) from fun p _ => ⟨Real.exp_pos _, mem_univ _⟩)
  simpa only [Function.comp_def, contDiffOn_univ] using h

end ForcedComputation.VelocityDetector

end

end OAI
