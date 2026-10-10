import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology

namespace WeakHessianFunctional

def heatSymbol (t s : ℝ) : ℝ :=
  if t = 0 then 1 else Real.exp t * expNegInvGlue (s / t)

@[simp] lemma heatSymbol_zero (s : ℝ) : heatSymbol 0 s = 1 := by simp [heatSymbol]

lemma heatSymbol_continuous (t : ℝ) : Continuous (heatSymbol t) := by
  unfold heatSymbol
  split_ifs
  · exact continuous_const
  · exact continuous_const.mul ((expNegInvGlue.contDiff (n := 0)).continuous.comp (continuous_id.div_const t))

lemma heatSymbol_nonneg (t s : ℝ) : 0 ≤ heatSymbol t s := by
  unfold heatSymbol
  split_ifs
  · exact zero_le_one
  · exact mul_nonneg (Real.exp_pos _).le (expNegInvGlue.nonneg _)

lemma heatSymbol_of_pos {t s : ℝ} (ht : 0 ≤ t) (hs : 0 < s) :
    heatSymbol t s = Real.exp (t-t/s) := by
  rcases ht.eq_or_lt with ht | ht
  · simp [← ht]
  · rw [heatSymbol, ite_eq_right ht.ne', expNegInvGlue, ite_eq_right (not_le.mpr (div_pos hs ht)),
      ← Real.exp_add, inv_div, sub_eq_add_neg]

lemma heatSymbol_nonpos {t s : ℝ} (ht : 0 < t) (hs : s ≤ 0) : heatSymbol t s = 0 := by
  rw [heatSymbol, ite_eq_right ht.ne', expNegInvGlue.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hs ht.le),
    mul_zero]

lemma heatSymbol_le_one {t s : ℝ} (ht : 0 ≤ t) (hs : s ≤ 1) : heatSymbol t s ≤ 1 := by
  rcases ht.eq_or_lt with ht | ht
  · simp [← ht]
  by_cases hsp : 0 < s
  · rw [heatSymbol_of_pos ht.le hsp, Real.exp_le_one_iff]
    have he : t ≤ t/s := (le_div_iff₀ hsp).mpr (by nlinarith)
    linarith
  · rw [heatSymbol_nonpos ht (not_lt.mp hsp)]
    exact zero_le_one

lemma heatSymbol_add {t u s : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) :
    heatSymbol (t+u) s = heatSymbol t s * heatSymbol u s := by
  rcases ht.eq_or_lt with ht | ht
  · simp [← ht]
  rcases hu.eq_or_lt with hu | hu
  · simp [← hu]
  by_cases hs : 0 < s
  · rw [heatSymbol_of_pos (by positivity) hs, heatSymbol_of_pos ht.le hs,
      heatSymbol_of_pos hu.le hs, ← Real.exp_add]
    congr 1
    ring
  · simp only [heatSymbol_nonpos ht (not_lt.mp hs),
      heatSymbol_nonpos hu (not_lt.mp hs), heatSymbol_nonpos (add_pos ht hu) (not_lt.mp hs), mul_zero]

lemma heatSymbol_resolvent_error {t s : ℝ} (ht : 0 ≤ t) (hs : s ∈ Icc (0:ℝ) 1) :
    |(heatSymbol t s - 1)*s| ≤ t := by
  rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr (heatSymbol_le_one ht hs.2)) hs.1)]
  rcases hs.1.eq_or_lt with hsz | hsz
  · simpa [← hsz] using ht
  rw [heatSymbol_of_pos ht hsz]
  have H := Real.add_one_le_exp (t-t/s)
  have H' := mul_le_mul_of_nonneg_right H hsz.le
  have he : (t/s)*s = t := div_mul_cancel₀ _ hsz.ne'
  nlinarith [mul_nonneg ht (sub_nonneg.mpr hs.2)]


open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def resolventHeat (R : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H := cfc (heatSymbol t) R

lemma resolventHeat_zero {R : H →L[ℂ] H} (hR : R.IsPositive) :
    resolventHeat R 0 = 1 := by
  change cfc (heatSymbol 0) R = 1
  have he : heatSymbol 0 = fun _ : ℝ => 1 := funext heatSymbol_zero
  rw [he, cfc_const 1 R hR.isSelfAdjoint, map_one]

lemma resolventHeat_add (R : H →L[ℂ] H) {t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) :
    resolventHeat R (t+u) = resolventHeat R t * resolventHeat R u := by
  change cfc (heatSymbol (t+u)) R = cfc (heatSymbol t) R*cfc (heatSymbol u) R
  rw [← cfc_mul _ _ _ (heatSymbol_continuous t).continuousOn
    (heatSymbol_continuous u).continuousOn]
  exact cfc_congr fun _ _ => heatSymbol_add ht hu

lemma resolvent_spectrum_bounds {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) {s : ℝ} (hs : s ∈ spectrum ℝ R) : s ∈ Icc (0:ℝ) 1 := by
  have h0 : 0 ≤ R := ContinuousLinearMap.nonneg_iff_isPositive.mpr hR
  have h1 : R ≤ 1 := ContinuousLinearMap.le_def.mpr hR1
  refine ⟨spectrum_nonneg_of_nonneg h0 hs, ?_⟩
  exact (le_algebraMap_iff_spectrum_le hR.isSelfAdjoint).mp (by simpa using h1) s hs

lemma resolventHeat_norm_le_one {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) {t : ℝ} (ht : 0 ≤ t) : ‖resolventHeat R t‖ ≤ 1 := by
  apply norm_cfc_le zero_le_one
  intro s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (heatSymbol_nonneg _ _)]
  exact heatSymbol_le_one ht (resolvent_spectrum_bounds hR hR1 hs).2

lemma resolventHeat_positive (R : H →L[ℂ] H) (t : ℝ) :
    (resolventHeat R t).IsPositive := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mp
  exact cfc_nonneg (fun s _ => heatSymbol_nonneg t s)

lemma resolventHeat_range_error {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) {t : ℝ} (ht : 0 ≤ t) :
    ‖(resolventHeat R t-1)*R‖ ≤ t := by
  have hb : ‖cfc (fun s => (heatSymbol t s-1)*s) R‖ ≤ t := by
    apply norm_cfc_le ht
    intro s hs
    exact heatSymbol_resolvent_error ht (resolvent_spectrum_bounds hR hR1 hs)
  rw [cfc_mul (fun s => heatSymbol t s-1) (fun s : ℝ => s) R ((heatSymbol_continuous t).sub continuous_const).continuousOn
    continuous_id.continuousOn, cfc_sub (heatSymbol t) (fun _ => 1) R (heatSymbol_continuous t).continuousOn
    continuous_const.continuousOn, cfc_const 1 R hR.isSelfAdjoint,
    map_one] at hb
  have hid : cfc (fun s : ℝ => s) R = R := cfc_id ℝ R hR.isSelfAdjoint
  rw [hid] at hb
  exact hb

lemma resolventHeat_range_error_apply {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) {t : ℝ} (ht : 0 ≤ t) (v : H) :
    ‖resolventHeat R t (R v)-R v‖ ≤ t*‖v‖ := by
  calc
    _ = ‖((resolventHeat R t-1)*R) v‖ := rfl
    _ ≤ ‖(resolventHeat R t-1)*R‖*‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ t*‖v‖ := mul_le_mul_of_nonneg_right (resolventHeat_range_error hR hR1 ht) (norm_nonneg _)

lemma resolventHeat_contractive {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) {t : ℝ} (ht : 0 ≤ t) (u v : H) :
    dist (resolventHeat R t u) (resolventHeat R t v) ≤ dist u v := by
  rw [dist_eq_norm, ← map_sub, dist_eq_norm]
  calc
    _ ≤ ‖resolventHeat R t‖ * ‖u-v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1*‖u-v‖ := mul_le_mul_of_nonneg_right (resolventHeat_norm_le_one hR hR1 ht) (norm_nonneg _)
    _ = _ := one_mul _

lemma resolventHeat_strong_zero {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) (hd : R.toLinearMap.range.topologicalClosure = ⊤) (u : H) :
    Tendsto (fun t : ℝ => resolventHeat R t u) (𝓝[≥] (0:ℝ)) (𝓝 u) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hd' := Submodule.dense_iff_topologicalClosure_eq_top.mpr hd
  obtain ⟨w, hw, hwR⟩ := Metric.dense_iff.mp hd' u (ε/4) (by positivity)
  obtain ⟨v,rfl⟩ := hwR
  have hv : dist (R v) u < ε/4 := hw
  have htend : Tendsto (fun t : ℝ => t*‖v‖) (𝓝[≥] (0:ℝ)) (𝓝 0) := by
    simpa using ((continuous_id.mul_const ‖v‖).continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto (fun t : ℝ => t*‖v‖) (𝓝[≥] (0:ℝ)) (𝓝 (0*‖v‖)))
  have hsmall : ∀ᶠ t : ℝ in 𝓝[≥] (0:ℝ), t*‖v‖ < ε/2 :=
    (tendsto_order.1 htend).2 _ (by positivity)
  filter_upwards [hsmall, self_mem_nhdsWithin] with t ht ht0
  have hn := resolventHeat_range_error_apply hR hR1 ht0 v
  have hcon := resolventHeat_contractive hR hR1 ht0 u (R v)
  have htri := dist_triangle (resolventHeat R t u) (resolventHeat R t (R v)) u
  have htri2 := dist_triangle (resolventHeat R t (R v)) (R v) u
  rw [dist_comm u (R v)] at hcon
  rw [dist_eq_norm (resolventHeat R t (R v)) (R v)] at htri2
  linarith

end WeakHessianFunctional

end

end OAI
