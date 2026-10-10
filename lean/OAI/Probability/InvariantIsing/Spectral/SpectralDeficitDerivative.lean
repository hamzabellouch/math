import OAI.Probability.InvariantIsing.Core.Variational
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace OAI

/-! Differentiating the overlap deficit away from atoms of the overlap law. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace InvariantIsing

/-- At every non-atom of the path law, the derivative of `D_p` is minus
the distribution function. This is the analytic step in `rot:function-path`. -/
theorem hasDerivAt_deficit_of_nonatom (p : OverlapPath) (r : ℝ)
    (hnonatom : pathMeasure {s | p s = r} = 0) :
    HasDerivAt (deficit p) (-pathMeasure.real {s | p s ≤ r}) r := by
  let A : Set ℝ := {s | p s ≤ r}
  have hA : MeasurableSet A := measurableSet_le p.measurable measurable_const
  let F : ℝ → ℝ → ℝ := fun t s => max (p s - t) 0
  let F' : ℝ → ℝ := fun s => A.indicator (fun _ => (1 : ℝ)) s - 1
  have hiA : Integrable (A.indicator (fun _ => (1 : ℝ))) pathMeasure :=
    (integrable_const (1 : ℝ)).indicator hA
  have hi' : Integrable F' pathMeasure := hiA.sub (integrable_const 1)
  have hmean : (∫ s, F' s ∂pathMeasure) = pathMeasure.real A - 1 := by
    dsimp [F']
    rw [integral_sub hiA (integrable_const 1), integral_indicator_const 1 hA]
    simp only [smul_eq_mul, mul_one, integral_const, measureReal_def,
      pathMeasure_univ, ENNReal.toReal_one]
  have hne : ∀ᵐ s ∂pathMeasure, p s ≠ r := by
    rw [ae_iff]
    simpa only [not_not] using hnonatom
  have hdiff : ∀ᵐ s ∂pathMeasure, HasDerivAt (F · s) (F' s) r := by
    filter_upwards [hne] with s hs
    rcases lt_or_gt_of_ne hs with h | h
    · have heq : (F · s) =ᶠ[𝓝 r] (fun _ => (0 : ℝ)) := by
        filter_upwards [Ioi_mem_nhds h] with t ht
        exact max_eq_right (sub_nonpos.mpr (show p s ≤ t from ht.le))
      have hd : HasDerivAt (F · s) 0 r :=
        (hasDerivAt_const r (0 : ℝ)).congr_of_eventuallyEq heq
      simpa only [F', indicator_of_mem (show s ∈ A from h.le), sub_self] using hd
    · have heq : (F · s) =ᶠ[𝓝 r] (fun t => p s - t) := by
        filter_upwards [Iio_mem_nhds h] with t ht
        exact max_eq_left (sub_nonneg.mpr (show t ≤ p s from ht.le))
      have hd : HasDerivAt (fun t : ℝ => p s - t) (-1) r := by
        convert! (hasDerivAt_const r (p s)).sub (hasDerivAt_id r) using 1
        ring
      have hd' := hd.congr_of_eventuallyEq heq
      simpa only [F', indicator_of_notMem (show s ∉ A from not_le.mpr h),
        zero_sub] using hd'
  have hlip : ∀ s, LipschitzWith 1 (F · s) := by
    intro s
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := abs_max_sub_max_le_abs (p s - x) (p s - y) 0
    have he : (p s - x) - (p s - y) = -(x - y) := by ring
    simpa only [F, Real.dist_eq, NNReal.coe_one, one_mul, he, abs_neg] using h
  have hmeas : ∀ᶠ t in 𝓝 r, AEStronglyMeasurable (F t) pathMeasure :=
    Eventually.of_forall fun _t =>
      ((p.measurable.sub measurable_const).max measurable_const).aestronglyMeasurable
  obtain ⟨_, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := pathMeasure) (F := F) (F' := F') (bound := fun _ => (1 : ℝ))
    (s := univ) univ_mem hmeas (p.integrable_posPart r) hi'.aestronglyMeasurable
    (ae_of_all _ fun s => by simpa using hlip s)
    (integrable_const 1) hdiff
  have hdD : HasDerivAt (deficit p) ((0 - 1) - ∫ s, F' s ∂pathMeasure) r := by
    convert! ((hasDerivAt_const r (1 : ℝ)).sub (hasDerivAt_id r)).sub hd using 1
  rw [hmean] at hdD
  convert hdD using 1
  ring

theorem ae_hasDerivAt_deficit (p : OverlapPath) :
    ∀ᵐ r ∂(volume : Measure ℝ),
      HasDerivAt (deficit p) (-pathMeasure.real {s | p s ≤ r}) r := by
  have hc : {r | 0 < pathMeasure {s | p s = r}}.Countable :=
    Measure.countable_meas_level_set_pos p.measurable
  filter_upwards [hc.ae_notMem (volume : Measure ℝ)] with r hr
  apply hasDerivAt_deficit_of_nonatom p r
  exact le_antisymm (le_of_not_gt hr) bot_le

end InvariantIsing

end

end OAI
