import OAI.Combinatorics.HalvingLines.Calculus

namespace OAI

namespace PlanarHalving

namespace RankLimit

open Filter MeasureTheory Set Metric
open scoped Topology

abbrev RatPoint := ℚ × ℚ

def ratPoint (q : RatPoint) : Point := ((q.1 : ℝ), (q.2 : ℝ))

noncomputable def lowerGrid (g : RatPoint → unitInterval) (x : Point) : unitInterval :=
  ⨆ q : RatPoint, if (q.1 : ℝ) < x.1 ∧ (q.2 : ℝ) < x.2 then g q else ⊥

lemma lowerGrid_monotone (g : RatPoint → unitInterval) : Monotone (lowerGrid g) := by
  intro x y hxy
  apply iSup_le
  intro q
  by_cases hq : (q.1 : ℝ) < x.1 ∧ (q.2 : ℝ) < x.2
  · have hqy : (q.1 : ℝ) < y.1 ∧ (q.2 : ℝ) < y.2 :=
      ⟨hq.1.trans_le hxy.1, hq.2.trans_le hxy.2⟩
    simpa only [lowerGrid, ite_eq_left hq, ite_eq_left hqy] using
      (le_iSup (fun r : RatPoint =>
        if (r.1 : ℝ) < y.1 ∧ (r.2 : ℝ) < y.2 then g r else ⊥) q)
  · simp only [ite_eq_right hq, bot_le]

lemma lowerGrid_measurable (g : RatPoint → unitInterval) : Measurable (lowerGrid g) := by
  apply Measurable.iSup
  intro q
  exact Measurable.ite
    ((isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt continuous_const continuous_snd)).measurableSet
    measurable_const measurable_const

lemma grid_le_lowerGrid {g : RatPoint → unitInterval} {q : RatPoint} {x : Point}
    (hq : (q.1 : ℝ) < x.1 ∧ (q.2 : ℝ) < x.2) : g q ≤ lowerGrid g x := by
  simpa only [lowerGrid, ite_eq_left hq] using
    (le_iSup (fun r : RatPoint =>
      if (r.1 : ℝ) < x.1 ∧ (r.2 : ℝ) < x.2 then g r else ⊥) q)

theorem moving_tendsto_of_grid {f : ℕ → Point → unitInterval}
    (hf : ∀ n, Monotone (f n)) {g : RatPoint → unitInterval}
    (hg : ∀ q, Tendsto (fun n => f n (ratPoint q)) atTop (𝓝 (g q)))
    {x : Point} (hc : ContinuousAt (lowerGrid g) x) {y : ℕ → Point}
    (hy : Tendsto y atTop (𝓝 x)) :
    Tendsto (fun n => f n (y n)) atTop (𝓝 (lowerGrid g x)) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    obtain ⟨q, hq⟩ := lt_iSup_iff.mp ha
    by_cases hqx : (q.1 : ℝ) < x.1 ∧ (q.2 : ℝ) < x.2
    · simp only [ite_eq_left hqx] at hq
      filter_upwards [(tendsto_order.mp (hg q)).1 a hq,
        (tendsto_order.mp ((continuous_fst.tendsto x).comp hy)).1 _ hqx.1,
        (tendsto_order.mp ((continuous_snd.tendsto x).comp hy)).1 _ hqx.2] with n hn hn₁ hn₂
      exact hn.trans_le (hf n ⟨hn₁.le, hn₂.le⟩)
    · simp only [ite_eq_right hqx, not_lt_bot] at hq
  · intro a ha
    have hn := hc.preimage_mem_nhds (isOpen_Iio.mem_nhds ha)
    obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp hn
    let b : Point := x + (δ / 2, δ / 2)
    have hb : b ∈ ball x δ := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [b, add_sub_cancel_left, Prod.norm_def, Real.norm_eq_abs,
        abs_of_pos (half_pos hδ), max_self]
      linarith only [hδ]
    have hba : lowerGrid g b < a := hδU hb
    obtain ⟨r₁, hxr₁, hr₁b⟩ := exists_rat_btwn
      (show x.1 < b.1 by dsimp [b]; linarith only [hδ])
    obtain ⟨r₂, hxr₂, hr₂b⟩ := exists_rat_btwn
      (show x.2 < b.2 by dsimp [b]; linarith only [hδ])
    let r : RatPoint := (r₁, r₂)
    have hra : g r < a := (grid_le_lowerGrid ⟨hr₁b, hr₂b⟩).trans_lt hba
    filter_upwards [(tendsto_order.mp (hg r)).2 a hra,
      (tendsto_order.mp ((continuous_fst.tendsto x).comp hy)).2 _ hxr₁,
      (tendsto_order.mp ((continuous_snd.tendsto x).comp hy)).2 _ hxr₂] with n hn hn₁ hn₂
    exact (hf n ⟨hn₁.le, hn₂.le⟩).trans_lt hn

theorem monotone_grid_subsequence {ι : Type*} [Countable ι]
    (f : ℕ → ι → Point → unitInterval) (hf : ∀ n i, Monotone (f n i)) :
    ∃ (φ : ℕ → ℕ) (F : ι → Point → unitInterval), StrictMono φ ∧
      (∀ i, Monotone (F i) ∧ Measurable (F i)) ∧
      (∀ i x, ContinuousAt (F i) x → ∀ y : ℕ → Point,
        Tendsto y atTop (𝓝 x) →
        Tendsto (fun n => f (φ n) i (y n)) atTop (𝓝 (F i x))) := by
  obtain ⟨g, φ, hφ, hg⟩ := CompactSpace.tendsto_subseq
    (fun n i q => f n i (ratPoint q))
  refine ⟨φ, fun i => lowerGrid (g i), hφ,
    fun i => ⟨lowerGrid_monotone _, lowerGrid_measurable _⟩, ?_⟩
  intro i x hx y hy
  apply moving_tendsto_of_grid (fun n => hf (φ n) i) _ hx hy
  intro q
  exact ((tendsto_pi_nhds.mp hg) i).apply_nhds q

end RankLimit

namespace Transversality

open MeasureTheory Set
open scoped MeasureTheory ENNReal

theorem critical_projection_null {Z : Type*} [MeasurableSpace Z]
    (σ : Measure Z) (coordinate : Z → Point) (hcoordinate : Measurable coordinate)
    (hdom : σ.map coordinate ≪ volume) (p : Z → Point) (F : Point → Point)
    (S : Set Z) (hidentity : ∀ z ∈ S, coordinate z = F (p z))
    (hdiff : ∀ z ∈ S, DifferentiableAt ℝ F (p z))
    (hsing : ∀ z ∈ S, (fderiv ℝ F (p z)).det = 0) : σ S = 0 := by
  obtain ⟨N, hsub, hN, hnull⟩ := exists_measurable_superset_of_null (critical_image_null F)
  apply measure_mono_null (t := coordinate ⁻¹' N)
  · intro z hz
    change coordinate z ∈ N
    rw [hidentity z hz]
    exact hsub ⟨p z, ⟨hdiff z hz, hsing z hz⟩, rfl⟩
  · rw [← Measure.map_apply hcoordinate hN]
    exact hdom hnull

theorem independent_gradients_ae {Z ι : Type*} [MeasurableSpace Z] [Countable ι]
    (ν : Measure Z) (h : Z → ℝ≥0∞) (hh : Measurable h)
    (σ : ι → Measure Z) (hν : ν.withDensity h ≪ Measure.sum σ)
    (coordinate : ι → Z → Point) (hcoordinate : ∀ i, Measurable (coordinate i))
    (hdom : ∀ i, (σ i).map (coordinate i) ≪ volume)
    (p : Z → Point) (F : ι → Point → Point) (S : Set Z)
    (hidentity : ∀ i z, z ∈ S → coordinate i z = F i (p z))
    (hdiff : ∀ i z, z ∈ S → DifferentiableAt ℝ (F i) (p z)) :
    ∀ᵐ z ∂ν, z ∈ S → h z ≠ 0 → ∃ i, (fderiv ℝ (F i) (p z)).det ≠ 0 := by
  have hbad : (ν.withDensity h) {z | z ∈ S ∧ ∀ i, (fderiv ℝ (F i) (p z)).det = 0} = 0 := by
    apply hν
    rw [Measure.sum_apply_eq_zero]
    intro i
    apply critical_projection_null (σ i) (coordinate i) (hcoordinate i) (hdom i) p
      (F i) _
    · intro z hz
      exact hidentity i z hz.1
    · intro z hz
      exact hdiff i z hz.1
    · intro z hz
      exact hz.2 i
  have hgood : ∀ᵐ z ∂ν.withDensity h,
      z ∈ S → ∃ i, (fderiv ℝ (F i) (p z)).det ≠ 0 := by
    apply ae_iff.mpr
    simpa only [Classical.not_imp, not_exists, not_not] using hbad
  have hg := (ae_withDensity_iff hh).mp hgood
  filter_upwards [hg] with z hz hzS hzh
  exact hz hzh hzS

end Transversality

end PlanarHalving

end OAI
