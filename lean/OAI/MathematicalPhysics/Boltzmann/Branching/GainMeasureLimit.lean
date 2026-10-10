import OAI.MathematicalPhysics.Boltzmann.Approximation.MassNormalizedCollisionLimits
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveVolterra
import OAI.MathematicalPhysics.Boltzmann.Branching.TwoCoreLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicFiniteGainStrong

namespace OAI

section

/-! # Doubling a positive gain kernel multiplies its nth iterate by two to the nth power -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.PositiveIteration

theorem iterate_add_self (a : ℝ) (K : Kernel KineticPhase Velocity) [IsSFiniteKernel K]
    {f : KineticPhase → ℝ≥0∞} (hf : Measurable f) (n : ℕ) :
    iterate a (K+K) f n = fun z => 2^n*iterate a K f n z := by
  induction n with
  | zero => simp only [iterate,pow_zero,one_mul]
  | succ n ih =>
    funext z
    change step a (K+K) (iterate a (K+K) f n) z = _
    rw [ih,step_const_mul a (K+K) _ (2^n) (by finiteness),
      step_add_kernel a K K (iterate_measurable a K hf n)]
    simp only [Pi.add_apply]
    change 2^n*(iterate a K f (n+1) z+iterate a K f (n+1) z) = _
    rw [pow_succ]
    ring

end BoltzmannNonuniqueness.PositiveIteration

end

end

section

/-! # Unnormalizing the convergent physical gain on a bounded velocity window -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
variable {ν : Measure Velocity} [IsFiniteMeasure ν]

theorem physical_gain_tendstoInMeasure
    {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ} {N : ℕ → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g)
    (hf : ∀ n p, 0 ≤ f n p) (hg : ∀ p, 0 ≤ g p)
    (hm : Tendsto (fun n => eLpNorm
      (fun x => fiberMass volume (f n) x-fiberMass volume g x) 1 μ) atTop (𝓝 0))
    (ha : Tendsto (fun n => eLpNorm (fun p =>
      gain (N n) (f n) p/(1+fiberMass volume (f n) p.1)-
      gainDensity g p/(1+fiberMass volume g p.1)) 1 (μ.prod ν)) atTop (𝓝 0)) :
    TendstoInMeasure (μ.prod ν) (fun n => gain (N n) (f n)) atTop (gainDensity g) := by
  have hrm n : Measurable (fiberMass volume (f n)) := fiberMass_measurable (hfm n)
  have hsm : Measurable (fiberMass volume g) := fiberMass_measurable hgm
  have hr : Tendsto (fun n => eLpNorm (fun p : X × Velocity =>
      fiberMass volume (f n) p.1-fiberMass volume g p.1) 1 (μ.prod ν)) atTop (𝓝 0) :=
    strongL1_comp_fst (fun n => (hrm n).sub hsm) hm
  have hr0 : ∀ n p, 0 ≤ fiberMass volume (f n) p := by
    intro n x
    exact integral_nonneg (fun v => hf n (x,v))
  have hs0 : ∀ x, 0 ≤ fiberMass volume g x := by
    intro x
    exact integral_nonneg (fun v => hg (x,v))
  exact tendstoInMeasure_of_strong_massNormalized (μ := μ.prod ν)
    (fun n => gain_measurable (N n) (hfm n))
    (fun n => (hrm n).comp measurable_fst) (fun n p => hr0 n p.1)
    (fun p => hs0 p.1) hr ha

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
