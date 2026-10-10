import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Piecewise

namespace OAI

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Invariant233

section ExponentialExtension

variable {X : Type*} [TopologicalSpace X] [T1Space X] [DecidableEq X]
variable (a : X) (g : X → ℝ)

theorem continuous_exp_neg_update
    (hc : ContinuousOn g ({a}ᶜ))
    (hlim : Tendsto g (𝓝[≠] a) atTop) :
    Continuous (Function.update (fun x => Real.exp (-g x)) a 0) := by
  classical
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = a
  · subst x
    rw [continuousAt_update_same]
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp hlim
  · rw [continuousAt_update_of_ne hx]
    have hgc : ContinuousAt g x :=
      (hc x hx).continuousAt (isOpen_compl_singleton.mem_nhds hx)
    exact Real.continuous_exp.continuousAt.comp hgc.neg

omit [TopologicalSpace X] [T1Space X] in

theorem exp_neg_update_mem_Icc (hg : ∀ x ≠ a, 0 ≤ g x) (x : X) :
    Function.update (fun y => Real.exp (-g y)) a 0 x ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  by_cases hx : x = a
  · subst x
    simp
  · rw [Function.update_of_ne hx]
    exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hg x hx))⟩

omit [TopologicalSpace X] [T1Space X] in

theorem exp_neg_update_eq_zero_iff (x : X) :
    Function.update (fun y => Real.exp (-g y)) a 0 x = 0 ↔ x = a := by
  classical
  by_cases hx : x = a
  · simp [hx]
  · simp [Real.exp_ne_zero, hx]

omit [TopologicalSpace X] [T1Space X] in

theorem neg_log_exp_neg_update (x : X) (hx : x ≠ a) :
    -Real.log (Function.update (fun y => Real.exp (-g y)) a 0 x) = g x := by
  classical
  simp [Function.update_of_ne hx, Real.log_exp]

end ExponentialExtension

section Integral

variable {X : Type*} [MeasurableSpace X] [DecidableEq X]
variable (μ : Measure X) (a : X) (g : X → ℝ)

theorem lintegral_neg_log_exp_neg_update (ha : μ {a} = 0) :
    (∫⁻ x, ENNReal.ofReal (-Real.log
      (Function.update (fun y => Real.exp (-g y)) a 0 x)) ∂μ) =
      ∫⁻ x, ENNReal.ofReal (g x) ∂μ := by
  classical
  apply lintegral_congr_ae
  have hne : ∀ᵐ x ∂μ, x ≠ a := by
    simpa only [ae_iff, not_not, Set.ofPred_eq_eq_singleton] using ha
  filter_upwards [hne] with x hx
  simp [Function.update_of_ne hx, Real.log_exp]

end Integral


variable {X : Type*} [TopologicalSpace X] [T1Space X] [MeasurableSpace X]

theorem exists_continuous_weight_of_cost
    (μ : Measure X) (a : X) (g : X → ℝ)
    (ha : μ {a} = 0)
    (hc : ContinuousOn g ({a}ᶜ))
    (hg : ∀ x ≠ a, 0 ≤ g x)
    (hlim : Tendsto g (𝓝[≠] a) atTop)
    (hint : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) = ∞) :
    ∃ f : X → ℝ, Continuous f ∧
      (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x, f x = 0 ↔ x = a) ∧
      (∀ x ≠ a, -Real.log (f x) = g x) ∧
      (∫⁻ x, ENNReal.ofReal (-Real.log (f x)) ∂μ) = ∞ := by
  classical
  refine ⟨Function.update (fun x => Real.exp (-g x)) a 0,
    continuous_exp_neg_update a g hc hlim,
    exp_neg_update_mem_Icc a g hg,
    exp_neg_update_eq_zero_iff a g,
    neg_log_exp_neg_update a g, ?_⟩
  rw [lintegral_neg_log_exp_neg_update μ a g ha, hint]


end Invariant233

end OAI
