import OAI.MathematicalPhysics.Boltzmann.Branching.CharacteristicCutoffGeometry
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.WithDensity

namespace OAI

section

/-! # Coordinate transport of the finite collision histories -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem transportedKernel_lintegral (e : X ≃ᵐ Y) (K : Kernel Y Y) (x : X)
    {f : X → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z, f z ∂transportedKernel e K x) = ∫⁻ y, f (e.symm y) ∂K (e x) := by
  rw [transportedKernel,Kernel.lintegral_map _ e.symm.measurable x hf,Kernel.comap_apply]

theorem transportedKernel_id (e : X ≃ᵐ Y) :
    transportedKernel e Kernel.id = Kernel.id := by
  apply Kernel.ext_fun
  intro x f hf
  have hc : Measurable (fun y => f (e.symm y)) := hf.comp e.symm.measurable
  rw [transportedKernel_lintegral e _ x hf,Kernel.id_apply,Kernel.id_apply,
    lintegral_dirac' _ hc,lintegral_dirac' _ hf]
  rw [e.symm_apply_apply]

theorem transportedKernel_compKernel (e : X ≃ᵐ Y) (K L : Kernel Y Y) :
    transportedKernel e (K ∘ₖ L) = transportedKernel e K ∘ₖ transportedKernel e L := by
  apply Kernel.ext_fun
  intro x f hf
  have hc : Measurable (fun y => f (e.symm y)) := hf.comp e.symm.measurable
  rw [transportedKernel_lintegral e _ x hf,
    Kernel.lintegral_comp _ _ _ hc,
    Kernel.lintegral_comp _ _ _ hf,
    transportedKernel_lintegral e _ x hf.lintegral_kernel]
  apply lintegral_congr
  intro y
  rw [transportedKernel_lintegral e _ _ hf,e.apply_symm_apply]

theorem transportedKernel_pow (e : X ≃ᵐ Y) (K : Kernel Y Y) (n : ℕ) :
    transportedKernel e (K^n) = (transportedKernel e K)^n := by
  induction n with
  | zero => exact transportedKernel_id e
  | succ n ih =>
    rw [show K^(n+1) = (K^n) ∘ₖ K by simpa only [pow_one] using Kernel.pow_add K n 1,
      transportedKernel_compKernel,ih]
    simpa only [pow_one] using (Kernel.pow_add (transportedKernel e K) n 1).symm

theorem transportedKernel_symm (e : X ≃ᵐ Y) (K : Kernel X X) :
    transportedKernel e (transportedKernel e.symm K) = K := by
  apply Kernel.ext_fun
  intro x f hf
  have hc : Measurable (fun y => f (e.symm y)) := hf.comp e.symm.measurable
  rw [transportedKernel_lintegral e _ x hf,
    transportedKernel_lintegral e.symm _ _ hc]
  simp only [MeasurableEquiv.symm_symm,MeasurableEquiv.symm_apply_apply]

end BoltzmannNonuniqueness

end

end

section

/-! # Constant density weights commute with a measurable change of kernel coordinates -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem transportedKernel_constDensity (e : X ≃ᵐ Y) (K : Kernel Y Y) [IsSFiniteKernel K]
    (c : ℝ) :
    transportedKernel e (K.withDensity (fun _ _ => ENNReal.ofReal c)) =
      (transportedKernel e K).withDensity (fun _ _ => ENNReal.ofReal c) := by
  apply Kernel.ext_fun
  intro x f hf
  have hc : Measurable (fun y => f (e.symm y)) := hf.comp e.symm.measurable
  rw [transportedKernel_lintegral e _ x hf,
    Kernel.lintegral_withDensity (f := fun (_ : Y) (_ : Y) => ENNReal.ofReal c) K
      (by fun_prop) (e x) hc,
    Kernel.lintegral_withDensity (f := fun (_ : X) (_ : X) => ENNReal.ofReal c)
      (transportedKernel e K) (by fun_prop) x hf,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    transportedKernel_lintegral e K x hf]

end BoltzmannNonuniqueness

end

end

section

/-! # Coordinate transport of a measurable output restriction -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem transportedKernel_restrict (e : X ≃ᵐ Y) (K : Kernel Y Y)
    {A : Set Y} (hA : MeasurableSet A) :
    transportedKernel e (K.restrict hA) = (transportedKernel e K).restrict (e.measurable hA) := by
  apply Kernel.ext_fun
  intro x f hf
  rw [transportedKernel_lintegral e _ x hf,Kernel.lintegral_restrict,
    ← lintegral_indicator hA,Kernel.lintegral_restrict,
    ← lintegral_indicator (e.measurable hA),
    transportedKernel_lintegral e K x (hf.indicator (e.measurable hA))]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ A
  · simp [hy]
  · simp [hy]

end BoltzmannNonuniqueness

end

end

end OAI
