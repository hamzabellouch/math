import OAI.Probability.InvariantIsing.Arrays.ReplicaProductPrimitives

namespace OAI

/-! Symbols determine bounded measurable paths up to a constant. A common
right root removes this constant, including jumps accumulating at zero. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace InvariantIsing

theorem equal_pathSymbols_constant_difference (a b : ℝ → ℝ)
    (ha : Measurable a) (hb : Measurable b) {A B : ℝ}
    (haB : ∀ u, |a u| ≤ A) (hbB : ∀ u, |b u| ≤ B) (da db : ℝ)
    (heq : ∀ s ∈ Ioo (0 : ℝ) 1, pathSymbol da a s = pathSymbol db b s)
    {s t : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    a s - b s = a t - b t := by
  let h : ℝ → ℝ := fun u => a u - b u
  let D := da - db
  let H : ℝ → ℝ := fun u => ∫ v in u..1, h v
  let G : ℝ → ℝ := fun u => (D - H u) / u
  have hhi (v w : ℝ) : IntervalIntegrable h volume v w :=
    intervalIntegrable_of_measurable_abs_le (ha.sub hb)
      (fun u => (abs_sub _ _).trans (add_le_add (haB u) (hbB u))) v w
  have hai (v w : ℝ) : IntervalIntegrable a volume v w :=
    intervalIntegrable_of_measurable_abs_le ha haB v w
  have hbi (v w : ℝ) : IntervalIntegrable b volume v w :=
    intervalIntegrable_of_measurable_abs_le hb hbB v w
  have hH : Continuous H := continuous_tail_integral hhi 1
  have hrel (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) : D - u * h u - H u = 0 := by
    have he := heq u hu
    unfold pathSymbol at he
    dsimp only [D, H, h]
    rw [intervalIntegral.integral_sub (hai u 1) (hbi u 1)]
    linarith
  have hid (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) : h u = G u := by
    apply (eq_div_iff hu.1.ne').mpr
    have he := hrel u hu
    linarith
  have hGd (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) : HasDerivAt G 0 u := by
    have hGc : ContinuousAt G u := (continuousAt_const.sub hH.continuousAt).div
      continuousAt_id hu.1.ne'
    have hhc : ContinuousAt h u := hGc.congr_of_eventuallyEq (by
      filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
      exact hid v hv)
    have hHd : HasDerivAt H (-h u) u := intervalIntegral.integral_hasDerivAt_left
      (hhi u 1) (ha.sub hb).stronglyMeasurable.stronglyMeasurableAtFilter hhc
    have hd := ((hasDerivAt_const u D).sub hHd).div (hasDerivAt_id u) hu.1.ne'
    change HasDerivAt G (((0 - -h u) * u - (D - H u) * 1) / u ^ 2) u at hd
    have hz : ((0 - -h u) * u - (D - H u) * 1) / u ^ 2 = 0 := by
      apply div_eq_zero_iff.mpr
      left
      have he := hrel u hu
      nlinarith
    rw [hz] at hd
    exact hd
  have hc := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun u hu => (hGd u hu).differentiableAt.differentiableWithinAt)
    (fun u hu => (hGd u hu).deriv) hs ht
  exact (hid s hs).trans (hc.trans (hid t ht).symm)

theorem equal_pathSymbols_equal_roots (a b : ℝ → ℝ)
    (ha : Measurable a) (hb : Measurable b) {A B : ℝ}
    (haB : ∀ u, |a u| ≤ A) (hbB : ∀ u, |b u| ≤ B) (da db r : ℝ)
    (heq : ∀ s ∈ Ioo (0 : ℝ) 1, pathSymbol da a s = pathSymbol db b s)
    (hra : Tendsto a (𝓝[>] 0) (𝓝 r)) (hrb : Tendsto b (𝓝[>] 0) (𝓝 r)) :
    da = db ∧ ∀ s ∈ Ioo (0 : ℝ) 1, a s = b s := by
  let c := a (1 / 2) - b (1 / 2)
  have hc (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) : a s - b s = c :=
    equal_pathSymbols_constant_difference a b ha hb haB hbB da db heq hs (by norm_num)
  have hce : (fun s => a s - b s) =ᶠ[𝓝[>] (0 : ℝ)] fun _ => c := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with s hs hlt
    exact hc s ⟨hs, hlt⟩
  have hlim : Tendsto (fun s => a s - b s) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self] using hra.sub hrb
  have hc0 : c = 0 := tendsto_nhds_unique (tendsto_const_nhds.congr' hce.symm) hlim
  have hab (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) : a s = b s := sub_eq_zero.mp ((hc s hs).trans hc0)
  refine ⟨?_, hab⟩
  have hi : (∫ u in (1 / 2 : ℝ)..1, a u) = ∫ u in (1 / 2 : ℝ)..1, b u := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro u hu
    exact hab u ⟨by linarith [hu.1], hu.2⟩
  have he := heq (1 / 2) (by norm_num)
  unfold pathSymbol at he
  rw [hab (1 / 2) (by norm_num), hi] at he
  linarith

end InvariantIsing

end

end OAI
