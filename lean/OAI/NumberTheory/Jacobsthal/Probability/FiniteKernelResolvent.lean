import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace OAI

namespace Erdos970

section

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory Topology BigOperators
namespace Erdos970Dependency.FiniteKernelResolvent
variable {X : Type*} [MeasurableSpace X]

theorem fixed_point_finite (Q : Kernel X X) (mu alpha : Measure X)
    (hfix : mu = alpha + Q ∘ₘ mu) (N : ℕ) :
    mu = (∑ j ∈ Finset.range N, (Q ^ j) ∘ₘ alpha) + (Q ^ N) ∘ₘ mu := by
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, pow_zero, zero_add]
    change mu = Kernel.id ∘ₘ mu
    exact Measure.id_comp.symm
  | succ N ih =>
    have hlast : (Q ^ N) ∘ₘ mu = (Q ^ N) ∘ₘ alpha + (Q ^ (N + 1)) ∘ₘ mu := by
      calc
        (Q ^ N) ∘ₘ mu = (Q ^ N) ∘ₘ (alpha + Q ∘ₘ mu) := congrArg (fun nu ↦ (Q ^ N) ∘ₘ nu) hfix
        _ = (Q ^ N) ∘ₘ alpha + ((Q ^ N) ∘ₖ Q) ∘ₘ mu := by rw [Measure.comp_add, Measure.comp_assoc]
        _ = _ := by rw [pow_succ]; rfl
    rw [Finset.sum_range_succ, add_assoc, ← hlast]
    exact ih

theorem residual_mass_tendsto_zero (Q : Kernel X X) (mu : Measure X) [IsFiniteMeasure mu]
    (hsub : ∀ n s, (Q ^ n) s univ ≤ 1)
    (htail : ∀ s, Tendsto (fun n : ℕ ↦ (Q ^ n) s univ) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ ((Q ^ n) ∘ₘ mu) univ) atTop (𝓝 0) := by
  have h := tendsto_lintegral_of_dominated_convergence (μ := mu)
    (F := fun n s ↦ (Q ^ n) s univ) (f := fun _ ↦ 0) (fun _ ↦ 1)
    (fun n ↦ (Q ^ n).measurable_coe MeasurableSet.univ)
    (fun n ↦ Eventually.of_forall (hsub n))
    (by simp) (Eventually.of_forall htail)
  have heq (n : ℕ) : ((Q ^ n) ∘ₘ mu) univ = ∫⁻ s, (Q ^ n) s univ ∂mu :=
    Measure.bind_apply MeasurableSet.univ (Q ^ n).aemeasurable
  simp_rw [heq]
  simpa only [lintegral_zero] using h

theorem residual_set_tendsto_zero (Q : Kernel X X) (mu : Measure X) [IsFiniteMeasure mu]
    (hsub : ∀ n s, (Q ^ n) s univ ≤ 1)
    (htail : ∀ s, Tendsto (fun n : ℕ ↦ (Q ^ n) s univ) atTop (𝓝 0)) (B : Set X) :
    Tendsto (fun n : ℕ ↦ ((Q ^ n) ∘ₘ mu) B) atTop (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (residual_mass_tendsto_zero Q mu hsub htail) (Eventually.of_forall (fun _ ↦ zero_le))
    (Eventually.of_forall (fun _ ↦ measure_mono (subset_univ B)))

theorem fixed_point_resolvent (Q : Kernel X X) (mu alpha : Measure X) [IsFiniteMeasure mu]
    (hfix : mu = alpha + Q ∘ₘ mu) (hsub : ∀ n s, (Q ^ n) s univ ≤ 1)
    (htail : ∀ s, Tendsto (fun n : ℕ ↦ (Q ^ n) s univ) atTop (𝓝 0)) :
    mu = Measure.sum (fun n : ℕ ↦ (Q ^ n) ∘ₘ alpha) := by
  ext B hB
  rw [Measure.sum_apply _ hB]
  have hfinite (N : ℕ) : mu B =
      (∑ j ∈ Finset.range N, ((Q ^ j) ∘ₘ alpha) B) + ((Q ^ N) ∘ₘ mu) B := by
    have h := congrArg (fun nu : Measure X ↦ nu B) (fixed_point_finite Q mu alpha hfix N)
    simpa only [Measure.add_apply, Measure.finsetSum_apply] using h
  have hlim := (ENNReal.tendsto_nat_tsum (fun n : ℕ ↦ ((Q ^ n) ∘ₘ alpha) B)).add
    (residual_set_tendsto_zero Q mu hsub htail B)
  simp only [add_zero] at hlim
  have hlim' : Tendsto (fun _ : ℕ ↦ mu B) atTop
      (𝓝 (∑' n : ℕ, ((Q ^ n) ∘ₘ alpha) B)) :=
    hlim.congr' (Eventually.of_forall (fun N ↦ (hfinite N).symm))
  exact tendsto_nhds_unique tendsto_const_nhds hlim'

end Erdos970Dependency.FiniteKernelResolvent

end

end Erdos970

end OAI
