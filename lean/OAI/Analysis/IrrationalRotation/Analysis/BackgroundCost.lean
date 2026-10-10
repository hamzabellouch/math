import Mathlib

namespace OAI

open scoped Topology BigOperators ENNReal
open Filter Set MeasureTheory

namespace Invariant233.BackgroundCost

theorem sum_le_one_of_disjoint_support {ι X : Type*} (s : Finset ι)
    (v : ι → X → ℝ) (hv : ∀ i x, v i x ≤ 1)
    (hd : Pairwise (fun i j => Disjoint (Function.support (v i))
      (Function.support (v j)))) (x : X) :
    (∑ i ∈ s, v i x) ≤ 1 := by
  classical
  by_cases h : ∃ i ∈ s, v i x ≠ 0
  · obtain ⟨i, hi, hix⟩ := h
    have hz : ∀ j ∈ s, j ≠ i → v j x = 0 := by
      intro j _ hji
      by_contra hjx
      exact Set.disjoint_left.mp (hd hji) hjx hix
    rw [Finset.sum_eq_single i (fun j hj hji => hz j hj hji)
      (fun hni => False.elim (hni hi))]
    exact hv i x
  · have hz : ∀ i ∈ s, v i x = 0 := by
      intro i hi
      by_contra hix
      exact h ⟨i, hi, hix⟩
    simp only [Finset.sum_eq_zero hz]
    norm_num

theorem average_bounds_of_disjoint_support {ι X : Type*} (s : Finset ι)
    (v : ι → X → ℝ) (hv0 : ∀ i x, 0 ≤ v i x) (hv1 : ∀ i x, v i x ≤ 1)
    (hd : Pairwise (fun i j => Disjoint (Function.support (v i))
      (Function.support (v j)))) {W : ℝ} (hW : 0 < W) (x : X) :
    0 ≤ (∑ i ∈ s, v i x) / W ∧ (∑ i ∈ s, v i x) / W ≤ 1 / W := by
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun i _ => hv0 i x) hW.le
  · exact div_le_div_of_nonneg_right
      (sum_le_one_of_disjoint_support s v hv1 hd x) hW.le

theorem continuous_negative_cost {X : Type*} [TopologicalSpace X]
    (w : ℕ → X → ℝ) (c : ℕ → ℝ) (hw : ∀ n, Continuous (w n))
    (hc : Summable c) (hbound : ∀ n x, ‖w n x‖ ≤ c n) :
    Continuous (fun x => ∑' n, w n x) :=
  continuous_tsum hw hc hbound

theorem continuousOn_tsum_of_locally_finite {X : Type*} [TopologicalSpace X]
    (v : ℕ → X → ℝ) (s : Set X) (hv : ∀ n, Continuous (v n))
    (hlocal : ∀ x ∈ s, ∃ t : Finset ℕ,
      ∀ᶠ y in 𝓝 x, ∀ n ∉ t, v n y = 0) :
    ContinuousOn (fun x => ∑' n, v n x) s := by
  intro x hx
  obtain ⟨t, ht⟩ := hlocal x hx
  have hfinite : Continuous (fun y => ∑ n ∈ t, v n y) :=
    continuous_finsetSum t (fun n _ => hv n)
  apply ContinuousAt.continuousWithinAt
  apply hfinite.continuousAt.congr_of_eventuallyEq
  exact ht.mono fun y hy => tsum_eq_sum hy

theorem locally_finite_of_support_shrinks {X : Type*} [MetricSpace X]
    (a : X) (v : ℕ → X → ℝ) (r : ℕ → ℝ)
    (hr : Tendsto r atTop (𝓝 0))
    (hsupp : ∀ n x, v n x ≠ 0 → dist x a ≤ r n) :
    ∀ x ≠ a, ∃ t : Finset ℕ,
      ∀ᶠ y in 𝓝 x, ∀ n ∉ t, v n y = 0 := by
  intro x hxa
  have hd : 0 < dist x a := dist_pos.mpr hxa
  have he : ∀ᶠ n in atTop, r n < dist x a / 2 :=
    hr.eventually (eventually_lt_nhds (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.1 he
  refine ⟨Finset.range N, ?_⟩
  filter_upwards [Metric.ball_mem_nhds x (show 0 < dist x a / 2 by linarith)]
    with y hy
  intro n hn
  have hn' : N ≤ n := Nat.le_of_not_gt (by simpa using hn)
  by_contra hv
  have hya := hsupp n y hv
  have hnsmall := hN n hn'
  have htri := dist_triangle x y a
  have hxy : dist x y < dist x a / 2 := by
    simpa [Metric.mem_ball, dist_comm] using hy
  linarith

theorem summable_of_support_shrinks {X : Type*} [MetricSpace X]
    (a : X) (v : ℕ → X → ℝ) (r : ℕ → ℝ)
    (hr : Tendsto r atTop (𝓝 0))
    (hsupp : ∀ n x, v n x ≠ 0 → dist x a ≤ r n)
    {x : X} (hx : x ≠ a) : Summable (fun n => v n x) := by
  obtain ⟨t, ht⟩ := locally_finite_of_support_shrinks a v r hr hsupp x hx
  exact summable_of_ne_finset_zero (mem_of_mem_nhds ht)

theorem hasSum_background_majorant :
    HasSum (fun n : ℕ => (1 : ℝ) / 2 ^ (n + 2)) (1 / 2) := by
  have h := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (1 / 4 : ℝ)
  have heq : (fun n : ℕ => (1 : ℝ) / 2 ^ (n + 2)) =
      (fun n : ℕ => (1 / 4 : ℝ) * (1 / 2) ^ n) := by
    funext n
    simp only [pow_add, div_pow, one_pow]
    norm_num
  rw [heq]
  simpa only [show (1 / 4 : ℝ) * (1 - 1 / 2)⁻¹ = 1 / 2 by norm_num] using h

theorem negative_cost_le {X : Type*} (w : ℕ → X → ℝ) (c : ℕ → ℝ)
    (hc : Summable c) (hw0 : ∀ n x, 0 ≤ w n x)
    (hwc : ∀ n x, w n x ≤ c n) (x : X) :
    (∑' n, w n x) ≤ ∑' n, c n := by
  have hw : Summable (fun n => w n x) :=
    Summable.of_nonneg_of_le (fun n => hw0 n x) (fun n => hwc n x) hc
  exact hw.tsum_le_tsum (fun n => hwc n x) hc

theorem background_cost_ge_half {X : Type*} (v w : ℕ → X → ℝ) (c : ℕ → ℝ)
    (hc : Summable c) (hcsum : (∑' n, c n) ≤ 1 / 2)
    (hv0 : ∀ n x, 0 ≤ v n x) (hw0 : ∀ n x, 0 ≤ w n x)
    (hwc : ∀ n x, w n x ≤ c n) (x : X) :
    1 / 2 ≤ 1 + (∑' n, v n x) - (∑' n, w n x) := by
  have hp : 0 ≤ ∑' n, v n x := tsum_nonneg (fun n => hv0 n x)
  have hn := (negative_cost_le w c hc hw0 hwc x).trans hcsum
  linarith

theorem background_cost_continuousOn {X : Type*} [MetricSpace X]
    (a : X) (v w : ℕ → X → ℝ) (r c : ℕ → ℝ)
    (hv : ∀ n, Continuous (v n)) (hw : ∀ n, Continuous (w n))
    (hr : Tendsto r atTop (𝓝 0))
    (hsupp : ∀ n x, v n x ≠ 0 → dist x a ≤ r n)
    (hc : Summable c) (hw0 : ∀ n x, 0 ≤ w n x)
    (hwc : ∀ n x, w n x ≤ c n) :
    ContinuousOn (fun x => 1 + (∑' n, v n x) - (∑' n, w n x)) {a}ᶜ := by
  have hp : ContinuousOn (fun x => ∑' n, v n x) {a}ᶜ :=
    continuousOn_tsum_of_locally_finite v _ hv
      (fun x hx => locally_finite_of_support_shrinks a v r hr hsupp x hx)
  have hn : Continuous (fun x => ∑' n, w n x) :=
    continuous_negative_cost w c hw hc (fun n x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hw0 n x)] using hwc n x)
  exact (continuousOn_const.add hp).sub hn.continuousOn

theorem tendsto_background_atTop {X : Type*} [TopologicalSpace X]
    (a : X) (v w : ℕ → X → ℝ) (c : ℕ → ℝ)
    (hv : ∀ n, Continuous (v n)) (hva : ∀ n, v n a = 1)
    (hv0 : ∀ n x, 0 ≤ v n x)
    (hvs : ∀ x, x ≠ a → Summable (fun n => v n x))
    (hc : Summable c) (hw0 : ∀ n x, 0 ≤ w n x)
    (hwc : ∀ n x, w n x ≤ c n) :
    Tendsto (fun x => 1 + (∑' n, v n x) - (∑' n, w n x))
      (𝓝[≠] a) atTop := by
  apply tendsto_atTop.2
  intro b
  obtain ⟨N, hN⟩ := exists_nat_gt (b + ∑' n, c n)
  have hpartial : Continuous (fun x => ∑ n ∈ Finset.range N, v n x) :=
    continuous_finsetSum _ (fun n _ => hv n)
  have hcenter : (∑ n ∈ Finset.range N, v n a) = (N : ℝ) := by
    simp [hva]
  have he : ∀ᶠ x in 𝓝 a,
      b + (∑' n, c n) ≤ ∑ n ∈ Finset.range N, v n x := by
    apply hpartial.continuousAt.eventually
    exact eventually_ge_nhds (by simpa [hcenter] using hN)
  filter_upwards [he.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with x hx hxa
  have hxa' : x ≠ a := hxa
  have hp : (∑ n ∈ Finset.range N, v n x) ≤ ∑' n, v n x :=
    (hvs x hxa').sum_le_tsum _ (fun n _ => hv0 n x)
  have hn := negative_cost_le w c hc hw0 hwc x
  linarith

theorem lintegral_bump_le_measure {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (v : X → ℝ) (s : Set X)
    (hv : ∀ x, v x ≤ 1) (hs : Function.support v ⊆ s) :
    (∫⁻ x, ENNReal.ofReal (v x) ∂μ) ≤ μ s := by
  apply (lintegral_mono (fun x => ?_)).trans (lintegral_indicator_one_le s)
  by_cases hx : x ∈ s
  · simpa only [Set.indicator_of_mem hx, Pi.one_apply] using
      (ENNReal.ofReal_le_one.2 (hv x))
  · have hz : v x = 0 := Function.support_subset_iff'.1 hs x hx
    simp only [Set.indicator_of_notMem hx, hz, ENNReal.ofReal_zero, le_refl]

theorem integrable_bump_series {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (v : ℕ → X → ℝ) (s : ℕ → Set X)
    (hv : ∀ n, Measurable (v n)) (hv0 : ∀ n x, 0 ≤ v n x)
    (hv1 : ∀ n x, v n x ≤ 1)
    (hsupp : ∀ n, Function.support (v n) ⊆ s n)
    (hsum : ∀ᵐ x ∂μ, Summable (fun n => v n x))
    (hμsum : (∑' n, μ (s n)) < ∞) :
    Integrable (fun x => ∑' n, v n x) μ := by
  refine ⟨AEStronglyMeasurable.tsum (fun n => (hv n).aestronglyMeasurable), ?_⟩
  rw [hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall (fun x => tsum_nonneg (fun n => hv0 n x)))]
  calc
    (∫⁻ x, ENNReal.ofReal (∑' n, v n x) ∂μ) =
        ∫⁻ x, ∑' n, ENNReal.ofReal (v n x) ∂μ := by
      apply lintegral_congr_ae
      exact hsum.mono (fun x hx => ENNReal.ofReal_tsum_of_nonneg (fun n => hv0 n x) hx)
    _ = ∑' n, ∫⁻ x, ENNReal.ofReal (v n x) ∂μ :=
      lintegral_tsum (fun n => (hv n).ennreal_ofReal.aemeasurable)
    _ ≤ ∑' n, μ (s n) := ENNReal.tsum_le_tsum
      (fun n => lintegral_bump_le_measure μ (v n) (s n) (hv1 n) (hsupp n))
    _ < ∞ := hμsum

theorem integrable_background_cost {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (v w : ℕ → X → ℝ)
    (s : ℕ → Set X) (c : ℕ → ℝ)
    (hv : ∀ n, Measurable (v n)) (hw : ∀ n, Measurable (w n))
    (hv0 : ∀ n x, 0 ≤ v n x) (hv1 : ∀ n x, v n x ≤ 1)
    (hsupp : ∀ n, Function.support (v n) ⊆ s n)
    (hvs : ∀ᵐ x ∂μ, Summable (fun n => v n x))
    (hμsum : (∑' n, μ (s n)) < ∞)
    (hc : Summable c) (hw0 : ∀ n x, 0 ≤ w n x)
    (hwc : ∀ n x, w n x ≤ c n) :
    Integrable (fun x => 1 + (∑' n, v n x) - (∑' n, w n x)) μ := by
  have hp := integrable_bump_series μ v s hv hv0 hv1 hsupp hvs hμsum
  have hn : Integrable (fun x => ∑' n, w n x) μ := by
    apply (integrable_const (∑' n, c n)).mono'
      (AEStronglyMeasurable.tsum (fun n => (hw n).aestronglyMeasurable))
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (fun n => hw0 n x))]
    exact negative_cost_le w c hc hw0 hwc x
  exact ((integrable_const (1 : ℝ)).add hp).sub hn

end Invariant233.BackgroundCost

end OAI
