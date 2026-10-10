import Mathlib

namespace OAI

open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace Invariant233.BackgroundCost

theorem exists_disjoint_closedBalls {ι X : Type*} [Finite ι] [MetricSpace X]
    (f : ι → X) (hf : Function.Injective f) :
    ∃ r : ℝ, 0 < r ∧ Pairwise (fun i j =>
      Disjoint (Metric.closedBall (f i) r) (Metric.closedBall (f j) r)) := by
  have hmul : Tendsto (fun r : ℝ => 2 * r) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun r : ℝ => 2 * r) := by fun_prop
    have h := hc.continuousAt (x := 0)
    change Tendsto (fun r : ℝ => 2 * r) (𝓝 0) (𝓝 (2 * 0)) at h
    simpa only [mul_zero] using h
  have he : ∀ᶠ r : ℝ in 𝓝 0, ∀ i j : ι, i ≠ j → 2 * r < dist (f i) (f j) := by
    apply eventually_all.2
    intro i
    apply eventually_all.2
    intro j
    by_cases hij : i = j
    · exact Eventually.of_forall (fun _ h => (h hij).elim)
    · have hd : 0 < dist (f i) (f j) := dist_pos.mpr (hf.ne hij)
      exact (hmul.eventually (eventually_lt_nhds hd)).mono fun _ h _ => h
  have hrpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  have he' : ∀ᶠ r : ℝ in 𝓝[>] 0,
      0 < r ∧ ∀ i j : ι, i ≠ j → 2 * r < dist (f i) (f j) :=
    hrpos.and (he.filter_mono nhdsWithin_le_nhds)
  obtain ⟨r, hr, hsep⟩ := he'.exists
  refine ⟨r, hr, ?_⟩
  intro i j hij
  apply Set.disjoint_left.2
  intro x hxi hxj
  have hi : dist (f i) x ≤ r := by
    simpa only [Metric.mem_closedBall, dist_comm] using hxi
  have hj : dist x (f j) ≤ r := hxj
  have ht := dist_triangle (f i) x (f j)
  have hs := hsep i j hij
  linarith

theorem exists_small_closedBall {X : Type*} [MetricSpace X]
    [MeasurableSpace X] (μ : Measure X) [μ.OuterRegular]
    [NullSingletonClass μ] (a : X) {R : ℝ} (hR : 0 < R)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ μ (Metric.closedBall a r) < ε := by
  obtain ⟨U, haU, hU, hμU⟩ :=
    Set.exists_isOpen_lt_of_lt (μ := μ) ({a} : Set X) ε (by simpa using hε)
  have ha : a ∈ U := haU (by simp)
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds ha)
  refine ⟨min (δ / 2) (R / 2), lt_min (by linarith) (by linarith), ?_, ?_⟩
  · exact (min_le_right _ _).trans_lt (by linarith)
  · apply lt_of_le_of_lt (measure_mono ?_) hμU
    intro x hx
    apply hδU
    have hd : dist x a ≤ δ / 2 := hx.trans (min_le_left _ _)
    show dist x a < δ
    linarith

theorem exists_tent_bump {X : Type*} [MetricSpace X] (a : X)
    {r : ℝ} (hr : 0 < r) :
    ∃ v : X → ℝ, Continuous v ∧ v a = 1 ∧
      (∀ x, 0 ≤ v x ∧ v x ≤ 1) ∧
      Function.support v ⊆ Metric.closedBall a r := by
  refine ⟨fun x => max (1 - dist x a / r) 0, ?_, ?_, ?_, ?_⟩
  · fun_prop
  · simp
  · intro x
    constructor
    · exact le_max_right _ _
    · apply max_le
      · have hd : 0 ≤ dist x a / r := div_nonneg dist_nonneg hr.le
        linarith
      · norm_num
  · intro x hx
    have hh : 0 < max (1 - dist x a / r) 0 :=
      lt_of_le_of_ne (le_max_right _ _) (Ne.symm hx)
    have hpos : 0 < 1 - dist x a / r := (lt_max_iff.mp hh).resolve_right (lt_irrefl _)
    have hd : dist x a < r := (div_lt_one hr).1 (by linarith)
    exact hd.le

theorem exists_bump_disjoint_images {ι X : Type*} [Finite ι] [MetricSpace X]
    [MeasurableSpace X] (μ : Measure X) [μ.OuterRegular]
    [NullSingletonClass μ] (a : X) (T : ι → X → X)
    (hT : ∀ i, Isometry (T i)) (ha : Function.Injective (fun i => T i a))
    {R : ℝ} (hR : 0 < R) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (r : ℝ) (v : X → ℝ), 0 < r ∧ r < R ∧
      μ (Metric.closedBall a r) < ε ∧ Continuous v ∧ v a = 1 ∧
      (∀ x, 0 ≤ v x ∧ v x ≤ 1) ∧
      Function.support v ⊆ Metric.closedBall a r ∧
      Pairwise (fun i j => Disjoint (T i '' Metric.closedBall a r)
        (T j '' Metric.closedBall a r)) := by
  obtain ⟨R₀, hR₀, hsep⟩ := exists_disjoint_closedBalls (fun i => T i a) ha
  obtain ⟨r, hr, hrR, hμr⟩ :=
    exists_small_closedBall μ a (lt_min hR hR₀) hε
  obtain ⟨v, hv, hva, hv01, hsupp⟩ := exists_tent_bump a hr
  refine ⟨r, v, hr, hrR.trans_le (min_le_left _ _), hμr,
    hv, hva, hv01, hsupp, ?_⟩
  have himage : ∀ i, T i '' Metric.closedBall a r ⊆ Metric.closedBall (T i a) R₀ := by
    intro i y hy
    obtain ⟨x, hx, rfl⟩ := hy
    show dist (T i x) (T i a) ≤ R₀
    rw [(hT i).dist_eq]
    exact hx.trans (hrR.le.trans (min_le_right _ _))
  intro i j hij
  exact (hsep hij).mono (himage i) (himage j)

theorem disjoint_support_comp_symm {ι X : Type*} (T : ι → X ≃ X)
    (v : X → ℝ) (s : Set X) (hs : Function.support v ⊆ s)
    (hd : Pairwise (fun i j => Disjoint (T i '' s) (T j '' s))) :
    Pairwise (fun i j => Disjoint
      (Function.support (fun x => v ((T i).symm x)))
      (Function.support (fun x => v ((T j).symm x)))) := by
  have hsub : ∀ i, Function.support (fun x => v ((T i).symm x)) ⊆ T i '' s := by
    intro i x hx
    exact ⟨(T i).symm x, hs hx, (T i).apply_symm_apply x⟩
  intro i j hij
  exact (hd hij).mono (hsub i) (hsub j)

end Invariant233.BackgroundCost

end OAI
