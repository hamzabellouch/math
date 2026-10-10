import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveSourceFormula
import OAI.MathematicalPhysics.Boltzmann.Branching.NormalGainMeasureActions
import Mathlib.Probability.Kernel.Composition.MeasureComp

namespace OAI

section

/-! # Monotonicity of the finite positive collision histories -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace BoltzmannNonuniqueness.KernelHistoryOrder

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

theorem comp_mono {K L : Kernel X Y} {M N : Kernel Y Z} (hK : K ≤ L) (hM : M ≤ N) :
    M ∘ₖ K ≤ N ∘ₖ L := by
  intro x
  apply Measure.le_iff.mpr
  intro A hA
  rw [Kernel.comp_apply' _ _ _ hA,Kernel.comp_apply' _ _ _ hA]
  exact (lintegral_mono (fun y => hM y A)).trans (lintegral_mono' (hK x) le_rfl)

theorem pow_mono {K L : Kernel X X} (h : K ≤ L) (n : ℕ) : K^n ≤ L^n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [pow_succ',pow_succ']
    exact comp_mono ih h

theorem measure_comp_mono {K L : Kernel X Y} {μ ν : Measure X}
    (hK : K ≤ L) (hμ : μ ≤ ν) : K ∘ₘ μ ≤ L ∘ₘ ν := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.bind_apply hA K.aemeasurable,Measure.bind_apply hA L.aemeasurable]
  exact (lintegral_mono (fun x => hK x A)).trans (lintegral_mono' hμ le_rfl)

end BoltzmannNonuniqueness.KernelHistoryOrder

end

end

section

/-! # A density-valued kernel integrated against its base measure -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem compProd_density_const (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    {f : X × Y → ℝ} (hf : Measurable f) :
    μ ⊗ₘ ((Kernel.const X ν).withDensity (fun x y => ENNReal.ofReal (f (x,y)))) =
      positiveDensityMeasure (μ.prod ν) f := by
  apply Measure.ext_of_lintegral
  intro g hg
  have hd : Measurable (Function.uncurry (fun x y => ENNReal.ofReal (f (x,y)))) :=
    hf.ennreal_ofReal
  let _ : IsSFiniteKernel ((Kernel.const X ν).withDensity
      (fun x y => ENNReal.ofReal (f (x,y)))) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)
  rw [Measure.lintegral_compProd hg,positiveDensityMeasure,
    lintegral_withDensity_eq_lintegral_mul _ hf.ennreal_ofReal hg,
    lintegral_prod _ (hf.ennreal_ofReal.mul hg).aemeasurable]
  apply lintegral_congr
  intro x
  rw [Kernel.withDensity_apply _ hd]
  exact lintegral_withDensity_eq_lintegral_mul _
    (hf.ennreal_ofReal.comp (measurable_const.prodMk measurable_id))
    (hg.comp (measurable_const.prodMk measurable_id))

end BoltzmannNonuniqueness

end

end

section

/-! # Kernels agreeing on a reachable region have identical finite histories there -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X]

theorem kernel_pow_eq_on_invariant (K L : Kernel X X) (A : Set X)
    (hinv : ∀ x ∈ A, ∀ᵐ y ∂K x, y ∈ A) (heq : ∀ x ∈ A, K x = L x)
    (n : ℕ) : ∀ x ∈ A, (K^n) x = (L^n) x := by
  induction n with
  | zero => intro x hx; rfl
  | succ n ih =>
    intro x hx
    rw [show K^(n+1) = (K^n) ∘ₖ K by simpa only [pow_one] using Kernel.pow_add K n 1,
      show L^(n+1) = (L^n) ∘ₖ L by simpa only [pow_one] using Kernel.pow_add L n 1,
      Kernel.comp_apply,Kernel.comp_apply]
    calc
      (K x).bind (K^n) = (K x).bind (L^n) := by
        apply Measure.bind_congr_right
        filter_upwards [hinv x hx] with y hy
        exact ih y hy
      _ = (L x).bind (L^n) := by rw [heq x hx]

end BoltzmannNonuniqueness

end

end

end OAI
