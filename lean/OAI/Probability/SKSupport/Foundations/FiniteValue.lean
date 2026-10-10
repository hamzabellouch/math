import Mathlib
import OAI.Probability.SKSupport.Backward.BackwardGradientSqJointBound
import OAI.Probability.SKSupport.Foundations.MeasurableSpatialDeriv

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma continuousOn_moving_heat_from {F : ℝ → ℝ → ℝ} {L : ℝ≥0} {p l u : ℝ}
    (hpl : p ≤ l) (hlu : l ≤ u) (hm : ∀ r, Measurable (F r))
    (hL : ∀ r ∈ Icc l u, ∀ s ∈ Icc l u, ∀ z y,
      |F r z-F s y| ≤ (L:ℝ)*(|r-s|+|z-y|)) (x : ℝ) :
    ContinuousOn (fun r => varianceHeat (r-p) (F r) x) (Icc l u) := by
  apply continuousOn_of_dominated
    (bound := fun y : ℝ => |F l x|+(L:ℝ)*((u-l)+Real.sqrt (u-p)*|y|))
  · intro r hr
    exact ((hm r).comp (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable
  · intro r hr
    filter_upwards [] with y
    have hh := hL r hr l ⟨le_rfl,hlu⟩ (x+Real.sqrt (r-p)*y) x
    have htri := abs_add_le (F r (x+Real.sqrt (r-p)*y)-F l x) (F l x)
    rw [sub_add_cancel] at htri
    rw [add_sub_cancel_left,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _),abs_of_nonneg (sub_nonneg.mpr hr.1)] at hh
    have hs : Real.sqrt (r-p) ≤ Real.sqrt (u-p) :=
      (Real.sqrt_le_sqrt_iff (sub_nonneg.mpr (hpl.trans hlu))).mpr (sub_le_sub_right hr.2 p)
    rw [Real.norm_eq_abs]
    change |F r (x+Real.sqrt (r-p)*y)| ≤ _
    have hmul := mul_le_mul_of_nonneg_right hs (abs_nonneg y)
    have hhi := mul_le_mul_of_nonneg_left (add_le_add (show r-l ≤ u-l by linarith [hr.2]) hmul) L.coe_nonneg
    linarith
  · exact (integrable_const _).add
      (((integrable_const _).add (integrable_standardGaussian_abs.const_mul _)).const_mul _)
  · filter_upwards [] with y
    exact (continuousOn_of_joint_bound hL).comp
      ((continuous_id.prodMk (continuous_const.add ((Real.continuous_sqrt.comp
        (continuous_id.sub continuous_const)).mul continuous_const))).continuousOn)
      (fun r hr => ⟨hr,Set.mem_univ _⟩)

lemma backward_heat_dual {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) {c : ℝ} (hc : 0 ≤ c) {p l u b : ℝ}
    (hl : 0 ≤ l) (hpl : p ≤ l) (hlu : l ≤ u) (hub : u ≤ b) (x : ℝ) :
    varianceHeat (u-p) (backward c b f u) x =
      varianceHeat (l-p) (backward c b f l) x-
        (c/2)*(∫ r in l..u, varianceHeat (r-p) (fun z => (deriv (backward c b f r) z)^2) x) := by
  obtain ⟨L,hL⟩ := backward_joint_bound hf hLip hc b
  obtain ⟨J,hJ⟩ := backward_gradient_sq_joint_bound hf hLip hc b
  have hinc : Icc l u ⊆ Icc 0 b := fun r hr => ⟨hl.trans hr.1,hr.2.trans hub⟩
  have hcont : ContinuousOn (fun r => varianceHeat (r-p) (backward c b f r) x) (Icc l u) :=
    continuousOn_moving_heat_from hpl hlu
      (fun r => (regularDatum_varianceLogHeat hf hLip hc (b-r)).smooth.continuous.measurable)
      (fun r hr s hs => hL r (hinc hr) s (hinc hs)) x
  have hscont := continuousOn_moving_heat_from hpl hlu
      (fun r => (regularDatum_varianceLogHeat hf hLip hc (b-r)).deriv_bounded.smooth.continuous.measurable.pow_const 2)
      (fun r hr s hs => hJ r (hinc hr) s (hinc hs)) x
  have hint : IntervalIntegrable (fun r => -(c/2)*varianceHeat (r-p)
      (fun z => (deriv (backward c b f r) z)^2) x) volume l u :=
    (hscont.const_mul (-(c/2))).intervalIntegrable_of_Icc hlu
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlu hcont
    (fun r hr => hasDerivAt_moving_backward_heat hf hLip hc (hpl.trans_lt hr.1) (hr.2.trans_le hub) x) hint
  rw [intervalIntegral.integral_const_mul] at he
  linarith

def finiteValue (c : ℕ → ℝ≥0) (h : ℝ≥0) (f : ℝ → ℝ) : ℕ → ℕ → ℝ → ℝ → ℝ
  | 0, _, _, x => f x
  | N+1, i, t, x => if t ≤ h then
      backward (c i) h (cascade c h f N (i+1)) t x
    else finiteValue c h f N (i+1) (t-h) x

def finiteCoeff (c : ℕ → ℝ≥0) (h : ℝ≥0) : ℕ → ℕ → ℝ → ℝ
  | 0, _, _ => 0
  | N+1, i, t => if t ≤ h then c i else finiteCoeff c h N (i+1) (t-h)

lemma finiteValue_regular {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) (t : ℝ) :
    RegularDatum (finiteValue c h f N i t) := by
  induction N generalizing i t with
  | zero => exact hf
  | succ N ih =>
    by_cases ht : t ≤ h
    · have he : finiteValue c h f (N+1) i t = backward (c i) h (cascade c h f N (i+1)) t := by
        funext x; simp only [finiteValue,ite_eq_left ht]
      rw [he]
      exact regularDatum_varianceLogHeat (cascade_regular hf hLip c h N (i+1))
        (cascade_lipschitz hLip c h N (i+1)) (c i).coe_nonneg (h-t)
    · have he : finiteValue c h f (N+1) i t = finiteValue c h f N (i+1) (t-h) := by
        funext x; simp only [finiteValue,ite_eq_right ht]
      rw [he]
      exact ih (i+1) (t-h)

lemma finiteValue_lipschitz {f : ℝ → ℝ} (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) (t : ℝ) :
    LipschitzWith 1 (finiteValue c h f N i t) := by
  induction N generalizing i t with
  | zero => exact hLip
  | succ N ih =>
    by_cases ht : t ≤ h
    · have he : finiteValue c h f (N+1) i t = varianceLogHeat (c i) (h-t) (cascade c h f N (i+1)) := by
        funext x; simp only [finiteValue,ite_eq_left ht,backward]
      rw [he]
      exact varianceLogHeat_lipschitz (cascade_lipschitz hLip c h N (i+1)) (c i).coe_nonneg _
    · have he : finiteValue c h f (N+1) i t = finiteValue c h f N (i+1) (t-h) := by
        funext x; simp only [finiteValue,ite_eq_right ht]
      rw [he]
      exact ih (i+1) (t-h)

lemma finiteValue_head (f : ℝ → ℝ) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) {t : ℝ}
    (ht : t ≤ h) : finiteValue c h f (N+1) i t = backward (c i) h (cascade c h f N (i+1)) t := by
  funext x; simp only [finiteValue,ite_eq_left ht]

lemma finiteValue_tail (f : ℝ → ℝ) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) {t : ℝ}
    (ht : (h:ℝ) < t) : finiteValue c h f (N+1) i t = finiteValue c h f N (i+1) (t-h) := by
  funext x; simp only [finiteValue,ite_eq_right (not_le.mpr ht)]

lemma finiteValue_zero {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) : finiteValue c h f N i 0 = cascade c h f N i := by
  cases N with
  | zero => rfl
  | succ N =>
    rw [finiteValue_head f c h N i h.coe_nonneg]
    funext x
    simp only [backward,sub_zero,cascade]
    exact varianceLogHeat_eq_logSemigroup (cascade_regular hf hLip c h N (i+1)).smooth.continuous.measurable (c i) h x

lemma measurable_finiteValue {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    Measurable (fun p : ℝ × ℝ => finiteValue c h f N i p.1 p.2) := by
  induction N generalizing i with
  | zero => exact hf.smooth.continuous.measurable.comp measurable_snd
  | succ N ih =>
    exact Measurable.ite (measurableSet_le measurable_fst measurable_const)
      (measurable_backward (cascade_regular hf hLip c h N (i+1)).smooth.continuous.measurable (c i) h)
      ((ih (i+1)).comp ((measurable_fst.sub_const (h:ℝ)).prodMk measurable_snd))

lemma measurable_finiteCoeff (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    Measurable (finiteCoeff c h N i) := by
  induction N generalizing i with
  | zero => exact measurable_const
  | succ N ih =>
    exact Measurable.ite (measurableSet_le measurable_id measurable_const)
      measurable_const ((ih (i+1)).comp (measurable_id.sub_const (h:ℝ)))

lemma finiteCoeff_bounds (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    ∃ C : ℝ≥0, ∀ t, 0 ≤ finiteCoeff c h N i t ∧ finiteCoeff c h N i t ≤ C := by
  induction N generalizing i with
  | zero => exact ⟨0,fun _ => ⟨le_rfl,le_rfl⟩⟩
  | succ N ih =>
    obtain ⟨C,hC⟩ := ih (i+1)
    refine ⟨c i+C,fun t => ?_⟩
    dsimp only [finiteCoeff]
    split_ifs with ht
    · constructor
      · exact (c i).coe_nonneg
      · simp only [NNReal.coe_add]; linarith [C.coe_nonneg]
    · constructor
      · exact (hC (t-h)).1
      · simp only [NNReal.coe_add]; linarith [(hC (t-h)).2,(c i).coe_nonneg]

lemma finiteValue_uniform_derivative_bounds {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i n : ℕ) :
    ∃ C : ℝ≥0, ∀ t x, |iteratedDeriv (n+1) (finiteValue c h f N i t) x| ≤ C := by
  induction N generalizing i with
  | zero =>
    obtain ⟨C,hC⟩ := hf.deriv_bounded.bounds n
    exact ⟨C,fun _ x => by simpa only [finiteValue,iteratedDeriv_succ'] using hC x⟩
  | succ N ih =>
    obtain ⟨C,hC⟩ := uniform_varianceLogHeat_derivative_bounds
      (cascade_regular hf hLip c h N (i+1)) (cascade_lipschitz hLip c h N (i+1)) (c i).coe_nonneg n
    obtain ⟨D,hD⟩ := ih (i+1)
    refine ⟨C+D,fun t x => ?_⟩
    by_cases ht : t ≤ h
    · rw [finiteValue_head f c h N i ht]
      rw [show backward (c i) h (cascade c h f N (i+1)) t =
        varianceLogHeat (c i) (h-t) (cascade c h f N (i+1)) from rfl]
      exact (hC (h-t) x).trans (by simp only [NNReal.coe_add]; linarith [D.coe_nonneg])
    · rw [finiteValue_tail f c h N i (lt_of_not_ge ht)]
      exact (hD (t-h) x).trans (by simp only [NNReal.coe_add]; linarith [C.coe_nonneg])

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
