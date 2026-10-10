import OAI.NumberTheory.Jacobsthal.Probability.FiniteKernelResolvent
import OAI.NumberTheory.Jacobsthal.Renewal.KernelPotential

namespace OAI

namespace Erdos970

section

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory Topology
namespace Erdos970Dependency.RegenerativeResolvent
open NumberTheoryLean.KernelPotential FiniteKernelResolvent
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem restrict_kernel_comp (P : Kernel X X) (mu : Measure X) {R : Set X} (hR : MeasurableSet R) :
    P.restrict hR ∘ₘ mu = (P ∘ₘ mu).restrict R := by
  ext B hB
  rw [Measure.bind_apply hB (P.restrict hR).aemeasurable, Measure.restrict_apply hB,
    Measure.bind_apply (hB.inter hR) P.aemeasurable]
  apply lintegral_congr
  intro s
  rw [Kernel.restrict_apply, Measure.restrict_apply hB]

theorem compose_sum_measure (B : Kernel X Y) (mu : ℕ → Measure X) :
    B ∘ₘ Measure.sum mu = Measure.sum (fun n ↦ B ∘ₘ mu n) := by
  ext S hS
  rw [Measure.bind_apply hS B.aemeasurable, lintegral_sum_measure, Measure.sum_apply _ hS]
  congr 1
  funext n
  exact (Measure.bind_apply hS B.aemeasurable).symm

theorem common_on_restriction (B : Kernel X Y) (mu : Measure X) {R : Set X}
    (hR : MeasurableSet R) (r : X) (hB : ∀ s ∈ R, B s = B r) :
    B ∘ₘ mu.restrict R = mu R • B r := by
  ext S hS
  rw [Measure.bind_apply hS B.aemeasurable, Measure.smul_apply, smul_eq_mul]
  calc
    (∫⁻ s, B s S ∂mu.restrict R) = ∫⁻ _s, B r S ∂mu.restrict R := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hR] with s hs
      rw [hB s hs]
    _ = _ := by simp [mul_comm]

theorem post_power_common (B : Kernel X Y) (Q : Kernel X X) (R : Set X) (r : X)
    (hB : ∀ s ∈ R, B s = B r) (hQ : ∀ s ∈ R, Q s = Q r) (n : ℕ) :
    ∀ s ∈ R, (B ∘ₖ (Q ^ n)) s = (B ∘ₖ (Q ^ n)) r := by
  intro s hs
  cases n with
  | zero =>
    change (B ∘ₖ Kernel.id) s = (B ∘ₖ Kernel.id) r
    rw [Kernel.comp_id]
    exact hB s hs
  | succ n =>
    rw [pow_succ]
    change (B ∘ₖ ((Q ^ n) ∘ₖ Q)) s = (B ∘ₖ ((Q ^ n) ∘ₖ Q)) r
    rw [← Kernel.comp_assoc]
    rw [Kernel.comp_apply, Kernel.comp_apply, hQ s hs]

theorem post_resolvent (B : Kernel X Y) (Q : Kernel X X) (mu : Measure X) [IsFiniteMeasure mu]
    (R : Set X) (hR : MeasurableSet R) (r : X)
    (hfix : mu = mu.restrict R + Q ∘ₘ mu)
    (hsub : ∀ n s, (Q ^ n) s univ ≤ 1)
    (htail : ∀ s, Tendsto (fun n : ℕ ↦ (Q ^ n) s univ) atTop (𝓝 0))
    (hB : ∀ s ∈ R, B s = B r) (hQ : ∀ s ∈ R, Q s = Q r) :
    B ∘ₘ mu = mu R • (potential B Q) r := by
  have hresolve := fixed_point_resolvent Q mu (mu.restrict R) hfix hsub htail
  calc
    B ∘ₘ mu = B ∘ₘ Measure.sum (fun n : ℕ ↦ (Q ^ n) ∘ₘ mu.restrict R) :=
      congrArg (fun nu ↦ B ∘ₘ nu) hresolve
    _ = Measure.sum (fun n : ℕ ↦ (B ∘ₖ (Q ^ n)) ∘ₘ mu.restrict R) := by
      rw [compose_sum_measure]
      congr 1
      funext n
      exact Measure.comp_assoc
    _ = Measure.sum (fun n : ℕ ↦ mu R • (B ∘ₖ (Q ^ n)) r) := by
      congr 1
      funext n
      exact common_on_restriction _ mu hR r (post_power_common B Q R r hB hQ n)
    _ = mu R • (potential B Q) r := by
      ext S hS
      rw [Measure.sum_apply _ hS, Measure.smul_apply, smul_eq_mul, potential, Kernel.sum_apply' _ _ hS]
      simp only [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.tsum_mul_left

end Erdos970Dependency.RegenerativeResolvent

end

end Erdos970

end OAI
