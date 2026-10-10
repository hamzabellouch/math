import OAI.Probability.InvariantIsing.Arrays.PathSymbolUniqueness

namespace OAI

/-! Almost-everywhere symbols determine the almost-everywhere path up to
one constant. This is the form needed after weak limiting Ward equations. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace InvariantIsing

theorem ae_equal_pathSymbols_constant_difference (a b : ℝ → ℝ)
    (ha : Measurable a) (hb : Measurable b) {A B : ℝ}
    (haB : ∀ u, |a u| ≤ A) (hbB : ∀ u, |b u| ≤ B) (da db : ℝ)
    (heq : ∀ᵐ s ∂pathMeasure, pathSymbol da a s = pathSymbol db b s) :
    ∃ c : ℝ, ∀ᵐ s ∂pathMeasure, a s - b s = c := by
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
  have hid : ∀ᵐ u ∂volume, u ∈ Ioo (0 : ℝ) 1 → h u = G u := by
    have he : ∀ᵐ u ∂volume, u ∈ Ioo (0 : ℝ) 1 →
        pathSymbol da a u = pathSymbol db b u :=
      (ae_restrict_iff' measurableSet_Ioo).mp heq
    filter_upwards [he] with u hu humem
    have heq := hu humem
    unfold pathSymbol at heq
    apply (eq_div_iff humem.1.ne').mpr
    change (a u - b u) * u = D - H u
    dsimp only [D, H, h]
    rw [intervalIntegral.integral_sub (hai u 1) (hbi u 1)]
    linarith
  have hGd (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) : HasDerivAt G 0 u := by
    have hGc : ContinuousAt G u := (continuousAt_const.sub hH.continuousAt).div
      continuousAt_id hu.1.ne'
    have hlocal : h =ᶠ[𝓝 u ⊓ ae volume] G := by
      filter_upwards [hid.filter_mono inf_le_right,
        Filter.Eventually.filter_mono inf_le_left (isOpen_Ioo.mem_nhds hu)] with v hv hvmem
      exact hv hvmem
    have hlim : Tendsto h (𝓝 u ⊓ ae volume) (𝓝 (G u)) :=
      (hGc.tendsto.mono_left inf_le_left).congr' hlocal.symm
    have hHd : HasDerivAt H (-G u) u := intervalIntegral.integral_hasDerivAt_of_tendsto_ae_left
      (hhi u 1) (ha.sub hb).stronglyMeasurable.stronglyMeasurableAtFilter hlim
    have hd := ((hasDerivAt_const u D).sub hHd).div (hasDerivAt_id u) hu.1.ne'
    change HasDerivAt G (((0 - -G u) * u - (D - H u) * 1) / u ^ 2) u at hd
    have hval : G u * u = D - H u := div_mul_cancel₀ _ hu.1.ne'
    have hz : ((0 - -G u) * u - (D - H u) * 1) / u ^ 2 = 0 := by
      apply div_eq_zero_iff.mpr
      left
      nlinarith
    rw [hz] at hd
    exact hd
  refine ⟨G (1 / 2), ?_⟩
  apply (ae_restrict_iff' measurableSet_Ioo).mpr
  filter_upwards [hid] with s hs hsmem
  have hc := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun u hu => (hGd u hu).differentiableAt.differentiableWithinAt)
    (fun u hu => (hGd u hu).deriv) hsmem (show (1 / 2 : ℝ) ∈ Ioo 0 1 by norm_num)
  exact (hs hsmem).trans hc

lemma ae_constant_right_root {h : ℝ → ℝ} {c r : ℝ}
    (he : ∀ᵐ s ∂pathMeasure, h s = c) (hr : Tendsto h (𝓝[>] 0) (𝓝 r)) : c = r := by
  by_contra hc
  have hp : 0 < |c - r| := abs_pos.mpr (sub_ne_zero.mpr hc)
  have hsmall : {s : ℝ | |h s - r| < |c - r|} ∈ 𝓝[>] (0 : ℝ) := by
    have ht := (hr.sub_const r).abs
    have hs := (tendsto_order.mp ht).2 _ (by simpa only [sub_self, abs_zero] using hp)
    exact hs
  obtain ⟨δ, hδ, hsub⟩ :=
    (mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset (show (0 : ℝ) < 1 by norm_num)).mp hsmall
  have hmono : Ioo (0 : ℝ) δ ⊆ Ioo (0 : ℝ) 1 := Ioo_subset_Ioo le_rfl hδ.2
  have heδ : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) δ), h s = c :=
    ae_mono (Measure.restrict_mono hmono le_rfl) he
  have hmass : volume (Ioo (0 : ℝ) δ) ≠ 0 := by
    rw [Real.volume_Ioo, sub_zero]
    exact (ENNReal.ofReal_pos.mpr hδ.1).ne'
  obtain ⟨s, hs, hsc⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hmass heδ
  have hh := hsub hs
  change |h s - r| < |c - r| at hh
  rw [hsc] at hh
  exact (lt_irrefl _) hh

theorem ae_equal_pathSymbols_equal_roots (a b : ℝ → ℝ)
    (ha : Measurable a) (hb : Measurable b) {A B : ℝ}
    (haB : ∀ u, |a u| ≤ A) (hbB : ∀ u, |b u| ≤ B) (da db r : ℝ)
    (heq : ∀ᵐ s ∂pathMeasure, pathSymbol da a s = pathSymbol db b s)
    (hra : Tendsto a (𝓝[>] 0) (𝓝 r)) (hrb : Tendsto b (𝓝[>] 0) (𝓝 r)) :
    da = db ∧ a =ᵐ[pathMeasure] b := by
  obtain ⟨c, hc⟩ := ae_equal_pathSymbols_constant_difference a b ha hb haB hbB da db heq
  have hlim : Tendsto (fun s => a s - b s) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self] using hra.sub hrb
  have hc0 : c = 0 := ae_constant_right_root hc hlim
  have hab : a =ᵐ[pathMeasure] b := by
    filter_upwards [hc] with s hs
    exact sub_eq_zero.mp (hs.trans hc0)
  refine ⟨?_, hab⟩
  have hunit : ∀ᵐ s ∂pathMeasure, s ∈ Ioo (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioo
  obtain ⟨s, hs, hsym, hsame⟩ := (hunit.and (heq.and hab)).exists
  have habv : ∀ᵐ u ∂volume, u ∈ Ioo (0 : ℝ) 1 → a u = b u :=
    (ae_restrict_iff' measurableSet_Ioo).mp hab
  have hi : (∫ u in s..1, a u) = ∫ u in s..1, b u := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [habv, volume.ae_ne (1 : ℝ)] with u hu hune humem
    rw [uIoc_of_le hs.2.le] at humem
    exact hu ⟨hs.1.trans humem.1, lt_of_le_of_ne humem.2 hune⟩
  unfold pathSymbol at hsym
  rw [hsame, hi] at hsym
  linarith

end InvariantIsing

end

end OAI
