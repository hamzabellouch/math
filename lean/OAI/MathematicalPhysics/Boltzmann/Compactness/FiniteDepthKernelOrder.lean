import OAI.MathematicalPhysics.Boltzmann.Collision.KernelInvariantOrder
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyIntegralBalance
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

section

/-! # Recovering the finite absolute-entropy datum class from relative entropy -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem FiniteEntropyDatum.of_relativeEntropy_integrable {f : Density}
    (hn : ∀ᵐ z, 0 ≤ f z) (hf : Integrable f)
    (hE : Integrable (fun z => ‖z.2‖^2*f z))
    (hH : Integrable (fun z => scalarRelativeEntropy (maxwellian z.2) (f z))) :
    FiniteEntropyDatum f := by
  have hlog : Integrable (fun z => f z*Real.log (f z)) := by
    have h := ((hH.add (hf.const_mul (1-(3/2:ℝ)*Real.log (2*Real.pi)))).sub
      (hE.const_mul (1/2:ℝ))).sub integrable_maxwellian_phase
    apply h.congr
    filter_upwards [] with z
    simp only [Pi.sub_apply,Pi.add_apply,scalarRelativeEntropy,log_maxwellian]
    ring
  refine ⟨hn,hf.aestronglyMeasurable,?_⟩
  apply ((hf.add hE).add hlog.norm).congr
  filter_upwards [hn] with z hz
  simp only [Pi.add_apply,Real.norm_eq_abs,abs_mul,abs_of_nonneg hz,entropyMoment]
  ring

theorem bounded_finiteEntropyDatum {q A p : ℝ} {f : Density}
    (hq : q < 2) (hA : 0 ≤ A) (hp : 1 < p)
    (hpi : Integrable (fun v : Velocity => H q v^p))
    (hfm : Measurable f) (hfn : ∀ z, 0 ≤ f z) (hfb : ∀ z, f z ≤ A*H q z.2) :
    FiniteEntropyDatum f := by
  have hfi : Integrable f := by
    apply (((integrable_H hq).const_mul A).comp_snd (volume : Measure Position)).mono'
      hfm.aestronglyMeasurable
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (hfn z)]
    exact hfb z
  have hEi : Integrable (fun z => ‖z.2‖^2*f z) := by
    have hmajor : Integrable (fun z : Phase => A*(‖z.2‖^2*H q z.2)) := by
      rw [Measure.volume_eq_prod]
      simpa only [Nat.reduceMul] using
        ((integrable_even_moment_H hq 1).const_mul A).comp_snd (volume : Measure Position)
    apply hmajor.mono' (((continuous_snd.norm.pow 2).measurable).mul hfm).aestronglyMeasurable
    filter_upwards [] with z
    simp only [Pi.mul_apply,Pi.pow_apply]
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hfn z))]
    exact (mul_le_mul_of_nonneg_left (hfb z) (sq_nonneg _)).trans_eq (by ring)
  have hHi : Integrable (fun z => scalarRelativeEntropy (maxwellian z.2) (f z)) := by
    rw [Measure.volume_eq_prod]
    exact bounded_relative_entropy_integrable hq hA hp hpi hfm hfn hfb
  exact FiniteEntropyDatum.of_relativeEntropy_integrable (Filter.Eventually.of_forall hfn) hfi hEi hHi

end BoltzmannNonuniqueness

end

end

section

/-! # Finite sums preserve convergence in integral L1 -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness.Compactness

theorem finite_integral_L1_zero {X ι : Type*} [MeasurableSpace X]
    {μ : Measure X} (s : Finset ι) {f : ι → ℕ → X → ℝ}
    (hi : ∀ i ∈ s, ∀ n, Integrable (f i n) μ)
    (hl : ∀ i ∈ s, Tendsto (fun n => ∫ x, |f i n x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, |∑ i ∈ s, f i n x| ∂μ) atTop (𝓝 0) := by
  have hb := tendsto_finsetSum s hl
  simp only [Finset.sum_const_zero] at hb
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => abs_nonneg _)) _ hb
  intro n
  calc
    _ ≤ ∫ x, ∑ i ∈ s, |f i n x| ∂μ := by
      apply integral_mono_of_nonneg (ae_of_all _ (fun _ => abs_nonneg _))
        (integrable_finsetSum s (fun i hi' => (hi i hi' n).abs))
      exact ae_of_all _ (fun x => Finset.abs_sum_le_sum_abs (fun i => f i n x) s)
    _ = _ := integral_finsetSum s (fun i hi' => (hi i hi' n).abs)

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Finite history comparison on a depth-dependent reachable region -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory
namespace BoltzmannNonuniqueness
variable {X : Type*} [MeasurableSpace X]

theorem kernel_pow_le_on_depth (K L : Kernel X X) (D : ℕ → Set X) (N : ℕ)
    (hstep : ∀ n < N, ∀ x ∈ D (n+1), ∀ᵐ y ∂K x, y ∈ D n)
    (hle : ∀ n < N, ∀ x ∈ D (n+1), K x ≤ L x) :
    ∀ n ≤ N, ∀ x ∈ D n, (K^n) x ≤ (L^n) x := by
  intro n hn
  induction n with
  | zero => intro x hx; exact le_rfl
  | succ n ih =>
    intro x hx
    have hnN : n < N := Nat.lt_of_succ_le hn
    rw [show K^(n+1) = (K^n) ∘ₖ K by simpa only [pow_one] using Kernel.pow_add K n 1,
      show L^(n+1) = (L^n) ∘ₖ L by simpa only [pow_one] using Kernel.pow_add L n 1]
    apply KernelHistoryOrder.measure_comp_mono_ae _ (hle n hnN x hx)
    filter_upwards [hstep n hnN x hx] with y hy
    exact ih (Nat.le_of_lt hnN) y hy

end BoltzmannNonuniqueness

end

end

end OAI
