import OAI.MathematicalPhysics.Boltzmann.Branching.AeKernelHistoryOrder
import Mathlib.Probability.Kernel.Composition.MeasureComp

namespace OAI

section

/-! # Finite sums commute with applying a kernel to a measure -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
namespace BoltzmannNonuniqueness
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem kernel_finset_comp_measure {ι : Type*} (I : Finset ι) (K : ι → Kernel X Y)
    (μ : Measure X) :
    ((∑ i ∈ I, K i) : Kernel X Y) ∘ₘ μ = ∑ i ∈ I, K i ∘ₘ μ := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih => simp only [Finset.sum_insert hi,Measure.add_comp,ih]

end BoltzmannNonuniqueness

end

end

section

/-! # Finite history comparison only needs kernel order on the reachable region -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X]

theorem kernel_pow_le_on_invariant (K L : Kernel X X) (A : Set X)
    (hinv : ∀ x ∈ A, ∀ᵐ y ∂K x, y ∈ A) (hle : ∀ x ∈ A, K x ≤ L x)
    (n : ℕ) : ∀ x ∈ A, (K^n) x ≤ (L^n) x := by
  induction n with
  | zero => intro x hx; exact le_rfl
  | succ n ih =>
    intro x hx
    rw [show K^(n+1) = (K^n) ∘ₖ K by simpa only [pow_one] using Kernel.pow_add K n 1,
      show L^(n+1) = (L^n) ∘ₖ L by simpa only [pow_one] using Kernel.pow_add L n 1]
    have h : ∀ᵐ y ∂K x, (K^n) y ≤ (L^n) y := by
      filter_upwards [hinv x hx] with y hy
      exact ih y hy
    exact KernelHistoryOrder.measure_comp_mono_ae h (hle x hx)

end BoltzmannNonuniqueness

end

end

end OAI
