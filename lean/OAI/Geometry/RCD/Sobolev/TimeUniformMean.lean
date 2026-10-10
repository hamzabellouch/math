import OAI.Geometry.RCD.Sobolev.ContinuousPathMean
import Mathlib.Topology.ContinuousMap.Compact

namespace OAI

/-! # A finite time grid upgrades pointwise mean errors to uniform path errors -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates

theorem finite_time_norm_control {δ : ℝ} (hδ : 0 < δ) :
    ∃ d : Finset Time, ∀ (f : C(Time,ℝ)) (L : ℝ≥0), LipschitzWith L f →
      ‖f‖ ≤ (L:ℝ)*δ+∑ t ∈ d, |f t| := by
  obtain ⟨d,_hd,hfin,hcover⟩ := (isCompact_univ : IsCompact (univ : Set Time)).finite_cover_balls hδ
  refine ⟨hfin.toFinset,?_⟩
  intro f L hL
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  obtain ⟨z,hz,htz⟩ := mem_iUnion₂.mp (hcover (mem_univ t))
  have hsum : |f z| ≤ ∑ y ∈ hfin.toFinset, |f y| :=
    Finset.single_le_sum (fun y _ => abs_nonneg (f y)) (hfin.mem_toFinset.mpr hz)
  have hdist := hL.dist_le_mul t z
  have htri := dist_triangle (f t) (f z) 0
  rw [dist_zero_right,dist_zero_right] at htri
  have hnear : dist t z < δ := htz
  calc
    ‖f t‖ ≤ dist (f t) (f z)+‖f z‖ := htri
    _ ≤ (L:ℝ)*δ+∑ y ∈ hfin.toFinset, |f y| :=
      add_le_add (hdist.trans (mul_le_mul_of_nonneg_left hnear.le L.coe_nonneg)) hsum

theorem time_uniform_mean_limit {A : Type*} [MeasurableSpace A]
    (μ : ℕ → Measure A) [∀ k, IsProbabilityMeasure (μ k)]
    (F : ℕ → A → C(Time,ℝ)) (M : ℝ≥0)
    (hI : ∀ k, Integrable (fun a => ‖F k a‖) (μ k))
    (hEval : ∀ k t, Integrable (fun a => F k a t) (μ k))
    (hLip : ∀ k, ∀ᵐ a ∂μ k, LipschitzWith M (F k a))
    (hpt : ∀ t : Time, Tendsto (fun k => ∫ a, |F k a t| ∂μ k) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ a, ‖F k a‖ ∂μ k) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro e he
  let δ := e/(2*((M:ℝ)+1))
  have hδ : 0 < δ := div_pos he (by positivity)
  have hδe : (M:ℝ)*δ < e/2 := by
    have hh : δ*(2*((M:ℝ)+1))=e := div_mul_cancel₀ e (by positivity)
    nlinarith [M.coe_nonneg]
  obtain ⟨d,hd⟩ := finite_time_norm_control hδ
  have hsum : Tendsto (fun k => ∑ t ∈ d, ∫ a, |F k a t| ∂μ k) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum d (fun t _ => hpt t)
  filter_upwards [(tendsto_order.mp hsum).2 (e/2) (half_pos he)] with k hk
  have hi : Integrable (fun a => (M:ℝ)*δ+∑ t ∈ d, |F k a t|) (μ k) :=
    (integrable_const _).add (integrable_finsetSum _ fun t _ => (hEval k t).abs)
  have hb := integral_mono_ae (hI k) hi ((hLip k).mono fun a ha => hd (F k a) M ha)
  rw [integral_add (integrable_const _) (integrable_finsetSum _ fun t _ => (hEval k t).abs),
    integral_const,smul_eq_mul,probReal_univ,one_mul,
    integral_finsetSum _ (fun t _ => (hEval k t).abs)] at hb
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg fun a => norm_nonneg (F k a))]
  linarith

end RegularPointCoordinates

end

end OAI
