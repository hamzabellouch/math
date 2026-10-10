import OAI.Analysis.KadisonKastler.ResolventMultiplierBounds
import OAI.Analysis.KadisonKastler.ResolventMultiplierLimit
import OAI.Analysis.KadisonKastler.ResolventVectorCutMeasure

namespace OAI

/-! # The cyclic model identifies the concrete cut projections -/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def resolventCutIndicator (R : H →L[ℂ] H) (r : ℝ) : spectrum ℝ R → ℂ :=
  {s : spectrum ℝ R | s.val < r}.indicator (fun _ => 1)

omit [CompleteSpace H] in
theorem resolventCutIndicator_measurable (R : H →L[ℂ] H) (r : ℝ) :
    Measurable (resolventCutIndicator R r) :=
  measurable_const.indicator (isOpen_lt continuous_subtype_val continuous_const).measurableSet

omit [CompleteSpace H] in
theorem resolventCutIndicator_bound (R : H →L[ℂ] H) (r : ℝ) (s : spectrum ℝ R) :
    ‖resolventCutIndicator R r s‖ ≤ 1 := by
  by_cases hs : s.val < r <;> simp [resolventCutIndicator, hs]

theorem resolventCyclicIsometry_cut (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (x : H) (r : ℝ) (v : ResolventCyclicL2 R hR x) :
    resolventCyclicIsometry R hR x
      (resolventScalarMultiplier R hR x (resolventCutIndicator R r)
        (resolventCutIndicator_measurable R r) 1 (resolventCutIndicator_bound R r) v) =
    resolventLowerCut R r (resolventCyclicIsometry R hR x v) := by
  let g : ℕ → C(spectrum ℝ R, ℝ) := fun n =>
    ⟨fun s => resolventCutScalar r (modularRegularizationScale n) s.val,
      (resolventCutScalar_continuous r (modularRegularizationScale_pos n)).comp
        continuous_subtype_val⟩
  let gc : ℕ → C(spectrum ℝ R, ℂ) := fun n =>
    ⟨fun s => (g n s : ℂ), Complex.continuous_ofReal.comp (g n).continuous⟩
  have hbn (n : ℕ) (s : spectrum ℝ R) : ‖gc n s‖ ≤ 1 := by
    change ‖(resolventCutScalar r (modularRegularizationScale n) s.val : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (resolventCutScalar_bounds r s.val (modularRegularizationScale_pos n)).1]
    exact (resolventCutScalar_bounds r s.val (modularRegularizationScale_pos n)).2
  have hpoint : ∀ s : spectrum ℝ R,
      Tendsto (fun n => gc n s) atTop (𝓝 (resolventCutIndicator R r s)) := by
    intro s
    have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (resolventCutScalar_tendsto r s.val)
    by_cases hs : s.val < r <;>
      simpa only [Function.comp_def, gc, g, ContinuousMap.coe_mk, resolventCutIndicator, Set.indicator,
        Set.mem_ofPred_eq, hs, ↓reduceIte, Complex.ofReal_one, Complex.ofReal_zero] using h
  have hl := resolventScalarMultiplier_tendsto R hR x (fun n => gc n)
    (resolventCutIndicator R r) (fun n => (gc n).continuous.measurable)
    (resolventCutIndicator_measurable R r) hbn (resolventCutIndicator_bound R r)
    (Eventually.of_forall hpoint) v
  have hcalc (n : ℕ) : resolventContinuousCalculus R hR (gc n) =
      resolventCutRegularization R r (modularRegularizationScale n) := by
    rw [resolventContinuousCalculus_ofReal R hR (g n), resolventCutRegularization,
      cfc_apply _ R hR (resolventCutScalar_continuous r (modularRegularizationScale_pos n)).continuousOn]
    rfl
  have he (n : ℕ) : resolventCyclicIsometry R hR x
      (resolventScalarMultiplier R hR x (gc n) (gc n).continuous.measurable 1 (hbn n) v) =
      resolventCutRegularization R r (modularRegularizationScale n)
        (resolventCyclicIsometry R hR x v) := by
    rw [resolventCyclicIsometry_multiplier_of_bound, hcalc]
  have ht := (resolventCyclicIsometry R hR x).continuous.continuousAt.tendsto.comp hl
  exact tendsto_nhds_unique ht
    ((resolventCutRegularization_tendsto R hR r (resolventCyclicIsometry R hR x v)).congr
      (fun n => (he n).symm))

end

end KadisonKastler

end OAI
