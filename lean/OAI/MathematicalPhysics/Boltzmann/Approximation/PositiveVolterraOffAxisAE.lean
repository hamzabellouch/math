import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveVolterra
import OAI.MathematicalPhysics.Boltzmann.Branching.OffAxisBoxExhaustion

namespace OAI

/-! # Representative invariance for the bounded off-axis positive iteration -/

noncomputable section

open MeasureTheory ProbabilityTheory
open BoltzmannNonuniqueness.Published
open scoped ENNReal

namespace BoltzmannNonuniqueness.PositiveIteration

theorem iterate_offAxis_congr_ae (hcarleman : Published.GPV2009CarlemanInput)
    (a q : ℝ) (c : Kernel SpaceTime Velocity) [IsSFiniteKernel c]
    {r : KineticPhase → ℝ≥0∞} (hr : Measurable r)
    (hc : ∀ x, c x = volume.withDensity (fun v => r (x,v)))
    {f g : KineticPhase → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hfg : f =ᵐ[((volume : Measure ℝ).prod volume).prod volume] g) (n : ℕ) :
    iterate a (ChartKernel.offAxis (ChartKernel.inputKernel c q)) f n
      =ᵐ[((volume : Measure ℝ).prod volume).prod volume]
    iterate a (ChartKernel.offAxis (ChartKernel.inputKernel c q)) g n := by
  induction n with
  | zero => exact hfg
  | succ n ih =>
    exact step_congr_ae a _ (iterate_measurable a _ hf n) (iterate_measurable a _ hg n)
      (ChartKernel.action_offAxis_normalized_congr_ae hcarleman _ c hr hc q
        (iterate_measurable a _ hf n) (iterate_measurable a _ hg n) ih)

theorem iterate_offAxis_congr_ae_at (hcarleman : Published.GPV2009CarlemanInput)
    (a q t : ℝ) (c : Kernel SpaceTime Velocity) [IsSFiniteKernel c]
    {r : KineticPhase → ℝ≥0∞} (hr : Measurable r)
    (hc : ∀ x, c x = volume.withDensity (fun v => r (x,v)))
    {f g : KineticPhase → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hfg : f =ᵐ[((volume : Measure ℝ).prod volume).prod volume] g) (n : ℕ) :
    (fun p : Velocity × Velocity =>
      iterate a (ChartKernel.offAxis (ChartKernel.inputKernel c q)) f (n+1) ((t,p.1),p.2))
      =ᵐ[volume]
    (fun p => iterate a (ChartKernel.offAxis (ChartKernel.inputKernel c q)) g (n+1) ((t,p.1),p.2)) := by
  apply step_congr_ae_at a t
  exact ChartKernel.action_offAxis_normalized_congr_ae hcarleman _ c hr hc q
    (iterate_measurable a _ hf n) (iterate_measurable a _ hg n)
    (iterate_offAxis_congr_ae hcarleman a q c hr hc hf hg hfg n)

end BoltzmannNonuniqueness.PositiveIteration

end

end OAI
