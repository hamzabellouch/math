import OAI.Analysis.KadisonKastler.ResolventVectorMeasure
import OAI.Analysis.KadisonKastler.ResolventCutMeasurable
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! # The vector measure of a resolvent cut -/

namespace KadisonKastler

open MeasureTheory Filter TopologicalSpace
open scoped Topology

noncomputable section

theorem resolventCutScalar_tendsto (r s : ℝ) :
    Tendsto (fun n => resolventCutScalar r (modularRegularizationScale n) s) atTop
      (𝓝 (if s < r then 1 else 0)) := by
  by_cases hs : s < r
  · have hm : 0 < r - s := sub_pos.mpr hs
    have hn : Tendsto (fun _ : ℕ => r - s) atTop (𝓝 (r - s)) := tendsto_const_nhds
    have ht := hn.div (hn.add modularRegularizationScale_tendsto) (by simpa using hm.ne')
    change Tendsto (fun n => (r - s) / (r - s + modularRegularizationScale n)) atTop
      (𝓝 ((r - s) / (r - s + 0))) at ht
    simpa only [resolventCutScalar, max_eq_left hm.le, ite_eq_left hs, add_zero,
      div_self hm.ne'] using ht
  · simpa only [resolventCutScalar, max_eq_right (sub_nonpos.mpr (le_of_not_gt hs)),
      zero_div, ite_eq_right hs] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem resolventVectorMeasure_cut (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (x : H) (r : ℝ) :
    (resolventVectorMeasure R hR x).real {s | s.val < r} = ‖resolventLowerCut R r x‖ ^ 2 := by
  let μ := resolventVectorMeasure R hR x
  let f := fun n (s : spectrum ℝ R) => resolventCutScalar r (modularRegularizationScale n) s.val
  have hi : Tendsto (fun n => ∫ s, f n s ∂μ) atTop
      (𝓝 (∫ s, {s : spectrum ℝ R | s.val < r}.indicator (fun _ => (1 : ℝ)) s ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    · intro n
      exact ((resolventCutScalar_continuous r (modularRegularizationScale_pos n)).comp
        continuous_subtype_val).aestronglyMeasurable
    · exact integrable_const 1
    · intro n
      exact Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs, abs_of_nonneg
          (resolventCutScalar_bounds r s.val (modularRegularizationScale_pos n)).1]
        exact (resolventCutScalar_bounds r s.val (modularRegularizationScale_pos n)).2
    · exact Eventually.of_forall fun s => by
        simpa only [Set.indicator, Set.mem_ofPred_eq] using resolventCutScalar_tendsto r s.val
  have he (n : ℕ) : (∫ s, f n s ∂μ) =
      (inner ℂ x (resolventCutRegularization R r (modularRegularizationScale n) x)).re := by
    rw [resolventCutRegularization, cfc_apply _ R hR
      (resolventCutScalar_continuous r (modularRegularizationScale_pos n)).continuousOn]
    exact resolventVectorMeasure_integral R hR x
      ⟨f n, (resolventCutScalar_continuous r (modularRegularizationScale_pos n)).comp
        continuous_subtype_val⟩
  have ht := ((show Continuous (fun y : H => inner ℂ x y) from
    continuous_const.inner continuous_id).tendsto (resolventLowerCut R r x)).comp
    (resolventCutRegularization_tendsto R hR r x)
  have hdiag : (inner ℂ x (resolventLowerCut R r x)).re = ‖resolventLowerCut R r x‖ ^ 2 := by
    have hs := inner_re_symm (𝕜 := ℂ) x (resolventLowerCut R r x)
    change (inner ℂ x (resolventLowerCut R r x)).re =
      (inner ℂ (resolventLowerCut R r x) x).re at hs
    rw [hs, resolventLowerCut_diagonal, ← Complex.ofReal_pow, Complex.ofReal_re]
  have hn := (Complex.continuous_re.tendsto _).comp ht
  simp only [Function.comp_def] at hn
  rw [hdiag] at hn
  simp only [he] at hi
  have hm : (∫ s, {s : spectrum ℝ R | s.val < r}.indicator (fun _ => (1 : ℝ)) s ∂μ) =
      μ.real {s | s.val < r} :=
    integral_indicator_one (isOpen_lt continuous_subtype_val continuous_const).measurableSet
  rw [hm] at hi
  exact tendsto_nhds_unique hi hn

end

end KadisonKastler

end OAI
