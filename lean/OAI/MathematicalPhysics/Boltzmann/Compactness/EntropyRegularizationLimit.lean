import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedEntropyProduction
import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedCollisionBlocks
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyIntegralBalance
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

section

/-! # Integrable bounded entropy tests on the phase and spacetime measures -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem measurable_boundedEntropyTest (n : ℕ) {m u : X → ℝ}
    (hm : Measurable m) (hu : Measurable u) :
    Measurable (fun x => boundedEntropyTest n (m x) (u x)) := by
  have hlog := (hu.div hm).log
  exact Measurable.ite (measurableSet_eq_fun hu measurable_const) measurable_const
    (Measurable.ite (measurableSet_le hlog.abs measurable_const) hlog measurable_const)

theorem measurable_entropyDual {m u s : X → ℝ}
    (hm : Measurable m) (hu : Measurable u) (hs : Measurable s) :
    Measurable (fun x => entropyDual (m x) (u x) (s x)) :=
  (hu.mul hs).sub (hm.mul (hs.exp.sub measurable_const))

theorem integrable_entropyDual {m u s : X → ℝ}
    (hm : Integrable m μ) (hu : Integrable u μ) (hs : Measurable s)
    {C : ℝ} (hC : ∀ x, |s x| ≤ C) :
    Integrable (fun x => entropyDual (m x) (u x) (s x)) μ := by
  have hfirst := hu.bdd_mul hs.aestronglyMeasurable (ae_of_all μ hC)
  have hbound : ∀ x, |Real.exp (s x)-1| ≤ Real.exp C+1 := by
    intro x
    calc
      |Real.exp (s x)-1| ≤ |Real.exp (s x)|+|1| := abs_sub _ _
      _ = Real.exp (s x)+1 := by rw [abs_of_pos (Real.exp_pos _),abs_one]
      _ ≤ Real.exp C+1 := add_le_add (Real.exp_le_exp.mpr ((le_abs_self _).trans (hC x))) le_rfl
  have hsecond := hm.bdd_mul (hs.exp.sub measurable_const).aestronglyMeasurable
    (ae_of_all μ hbound)
  simpa only [entropyDual,mul_comm,Pi.sub_def,Pi.mul_def] using hfirst.sub hsecond

end BoltzmannNonuniqueness

end

end

section

/-! # Removing Gaussian regularization from the integrated relative entropy -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X]

theorem gaussianRegularized_entropy_tendsto {μ : Measure X} [IsFiniteMeasure μ]
    {q A p : ℝ} (hq : q < 2) (hA : 0 ≤ A) (hp : 1 < p)
    (hpi : Integrable (fun v : Velocity => H q v^p))
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hfn : ∀ z, 0 ≤ f z)
    (hfb : ∀ z, f z ≤ A*H q z.2) :
    Tendsto (fun δ : ℝ => ∫ z, scalarRelativeEntropy (maxwellian z.2)
      (gaussianRegularizedDensity δ f z) ∂μ.prod volume)
      (𝓝[>] 0) (𝓝 (∫ z, scalarRelativeEntropy (maxwellian z.2) (f z) ∂μ.prod volume)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun z : X × Velocity => entropyPowerMajorant q (A+tiltConstant) p z.2)
  · exact Eventually.of_forall (fun δ => by
      have hm : Measurable (fun z => scalarRelativeEntropy (maxwellian z.2)
          (gaussianRegularizedDensity δ f z)) := by
        have hg := gaussianRegularizedDensity_measurable δ hfm
        unfold scalarRelativeEntropy maxwellian
        fun_prop
      exact hm.aestronglyMeasurable)
  · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with δ hδ
    filter_upwards [] with z
    have hn : 0 ≤ gaussianRegularizedDensity δ f z :=
      add_nonneg (hfn z) (mul_nonneg hδ.1.le (Real.exp_nonneg _))
    have hb : gaussianRegularizedDensity δ f z ≤ (A+tiltConstant)*H q z.2 :=
      gaussianRegularization_bound hδ.1.le hδ.2.le (fun v => hfb (z.1,v)) z.2
    rw [Real.norm_of_nonneg (scalarRelativeEntropy_nonneg (maxwellian_pos _) hn)]
    exact scalarRelativeEntropy_le_majorant (add_nonneg hA tiltConstant_pos.le) hp z.2 hn hb
  · exact (entropyPowerMajorant_integrable (B := A+tiltConstant) hq hpi).comp_snd μ
  · filter_upwards [] with z
    have hc : Continuous (fun δ : ℝ => scalarRelativeEntropy (maxwellian z.2)
        (f z+δ*Real.exp (-2*‖z.2‖^2))) :=
      (scalarRelativeEntropy_continuous _).comp (continuous_const.add (continuous_id.mul_const _))
    simpa only [gaussianRegularizedDensity,zero_mul,add_zero] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds

theorem regularizedRelativeEntropyDensity_tendsto {q A p : ℝ}
    (hq : q < 2) (hA : 0 ≤ A) (hp : 1 < p)
    (hpi : Integrable (fun v : Velocity => H q v^p))
    {f : Density} (hfm : Measurable f) (hfn : ∀ z, 0 ≤ f z)
    (hfb : ∀ z, f z ≤ A*H q z.2) :
    Tendsto (fun δ : ℝ => ∫ z, regularizedRelativeEntropyDensity δ f z)
      (𝓝[>] 0) (𝓝 (∫ z, scalarRelativeEntropy (maxwellian z.2) (f z))) := by
  rw [Measure.volume_eq_prod]
  exact gaussianRegularized_entropy_tendsto hq hA hp hpi hfm hfn hfb

end BoltzmannNonuniqueness

end

end

end OAI
