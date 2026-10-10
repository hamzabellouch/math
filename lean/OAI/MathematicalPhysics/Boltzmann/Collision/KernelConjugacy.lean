import OAI.MathematicalPhysics.Boltzmann.Branching.TransportedKernelRestriction

namespace OAI

/-! # Iteration commutes with an exact measurable change of coordinates -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem kernel_eq_transport_of_map (e : X ≃ᵐ Y) (K : Kernel X X) (L : Kernel Y Y)
    (h : ∀ x, (K x).map e = L (e x)) : K = transportedKernel e L := by
  apply Kernel.ext_fun
  intro x f hf
  have hc : Measurable (fun y => f (e.symm y)) := hf.comp e.symm.measurable
  have H := congrArg (fun μ : Measure Y => ∫⁻ y, f (e.symm y) ∂μ) (h x)
  rw [lintegral_map hc e.measurable] at H
  rw [transportedKernel_lintegral e L x hf]
  simpa only [MeasurableEquiv.symm_apply_apply] using H

theorem transportedKernel_map (e : X ≃ᵐ Y) (L : Kernel Y Y) (x : X) :
    (transportedKernel e L x).map e = L (e x) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hc : Measurable (fun x => f (e x)) := hf.comp e.measurable
  rw [lintegral_map hf e.measurable,transportedKernel_lintegral e L x hc]
  simp only [MeasurableEquiv.apply_symm_apply]

theorem kernel_pow_map (e : X ≃ᵐ Y) (K : Kernel X X) (L : Kernel Y Y)
    (h : ∀ x, (K x).map e = L (e x)) (n : ℕ) (x : X) :
    ((K^n) x).map e = (L^n) (e x) := by
  rw [kernel_eq_transport_of_map e K L h,← transportedKernel_pow]
  exact transportedKernel_map e (L^n) x

end BoltzmannNonuniqueness

end

end OAI
