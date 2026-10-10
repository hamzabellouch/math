import OAI.Probability.SLE.Gauge.UniformRibbonStep

namespace OAI

/-! An actual successful passage gives another admissible stopped ribbon
history. Inverse coordinates are used only on the compact physical patch
where the successful path is contained. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open RibbonCoordinates BoundaryScaleLaw FirstFrontPassage PassageSuccess

lemma strict_before_attained_front
    (x : ℝ≥0 → ℝ) (q : ℝ) (S : ℝ≥0)
    (hc : ContinuousOn x (Icc 0 S)) (h0 : x 0 < q)
    (hfirst : firstFrontTime x q = (S : WithTop ℝ≥0)) :
    ∀ t : ℝ≥0, t < S → x t < q := by
  intro t ht
  by_contra hn
  obtain ⟨u, hu, hue⟩ := intermediate_value_Icc (show (0 : ℝ≥0) ≤ t from bot_le)
    (hc.mono (Icc_subset_Icc_right ht.le)) ⟨h0.le, le_of_not_gt hn⟩
  have hh := hittingAfter_le_of_mem (u := fun t (_ : Unit) => x t - q)
    (ω := ()) (show (0 : ℝ≥0) ≤ u from bot_le)
    (show x u - q ∈ ({0} : Set ℝ) by simp only [hue, sub_self, mem_singleton_iff])
  change firstFrontTime x q ≤ (u : WithTop ℝ≥0) at hh
  rw [hfirst, WithTop.coe_le_coe] at hh
  exact (not_le_of_gt ht) (hh.trans hu.2)

def RibbonHistory.futureCoordinates {C L : ℝ≥0} {ε : ℝ}
    (d : RibbonHistory C L ε) (t : ℝ≥0) : ℂ :=
  (d.front : ℂ) + coordinateInverse d.stepChart ribbonStepCompact (d.trace (d.time + t))

def RibbonHistory.advanceCoordinates {C L : ℝ≥0} {ε : ℝ}
    (d : RibbonHistory C L ε) (t : ℝ≥0) : ℂ :=
  if t ≤ d.time then d.coordinates (min t d.time) else d.futureCoordinates (t - d.time)

def RibbonHistory.futureTrace {C L : ℝ≥0} {ε : ℝ}
    (d : RibbonHistory C L ε) : C(ℝ≥0, ℂ) :=
  ⟨fun t => d.trace (d.time + t),
    d.witness.1.comp (continuous_const.add continuous_id)⟩

lemma RibbonHistory.tip_in_stepCompact {C L : ℝ≥0} {ε : ℝ}
    (d : RibbonHistory C L ε) (hε : ε ≤ 1 / 8) :
    (d.offset : ℂ) * Complex.I ∈ ribbonStepCompact := by
  change -(1 / 2 : ℝ) ≤ ((d.offset : ℂ) * Complex.I).re ∧
    ((d.offset : ℂ) * Complex.I).re ≤ 5 / 2 ∧
    |((d.offset : ℂ) * Complex.I).im| ≤ 1 / 2
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, sub_self, Complex.mul_im, mul_one, add_zero]
  exact ⟨by norm_num, by norm_num, by linarith [d.offset_bound]⟩

lemma RibbonHistory.futureCoordinates_zero {C L : ℝ≥0} {ε : ℝ}
    (d : RibbonHistory C L ε) (hε : ε ≤ 1 / 8) :
    d.futureCoordinates 0 = d.coordinates d.time := by
  have htip : d.trace d.time = d.stepChart ((d.offset : ℂ) * Complex.I) := by
    rw [RibbonHistory.stepChart, ← d.attained]
    exact d.trace_coordinates ⟨bot_le, le_rfl⟩
  simp only [RibbonHistory.futureCoordinates, add_zero, htip,
    coordinateInverse_left (lower_lipschitz_injOn _ _ L d.step_lower)
      (d.tip_in_stepCompact hε), d.attained]

/-- The completed actual trace retains continuous ribbon coordinates,
the narrow core, and the strict first-front property required for the
next application of the uniform step theorem. -/
theorem RibbonHistory.successful_continuation
    {C L : ℝ≥0} {ε : ℝ} (d : RibbonHistory C L ε)
    (hε : ε ≤ 1 / 8) (hL : 0 < L)
    (S : ℝ≥0)
    (hfirst : firstFrontTime
      (fun t => longitudinalCoordinate d.chart closedRibbon d.front
        (d.trace (d.time + t))) 1 = (S : WithTop ℝ≥0))
    (hhit : longitudinalCoordinate d.chart closedRibbon d.front
      (d.trace (d.time + S)) = 1)
    (hS : 0 < S)
    (hpath : MapsTo (fun t => d.trace (d.time + t)) (Icc 0 S)
      (physicalPassageRegion d.stepChart ribbonStepCompact C ε (ε / L)))
    (hoffset : ‖d.trace (d.time + S) - d.chart ((d.front : ℂ) + 1)‖ < (ε / L) / 4) :
    ContinuousOn d.advanceCoordinates (Icc 0 (d.time + S)) ∧
    EqOn d.trace (d.chart ∘ d.advanceCoordinates) (Icc 0 (d.time + S)) ∧
    (d.advanceCoordinates 0).re = 0 ∧
    d.advanceCoordinates (d.time + S) =
      ((d.front + 1 : ℝ) : ℂ) + ((d.futureCoordinates S).im : ℂ) * Complex.I ∧
    |(d.futureCoordinates S).im| ≤ ε / 4 ∧
    MapsTo d.advanceCoordinates (Icc 0 (d.time + S)) closedRibbon ∧
    (∀ t ∈ Icc 0 (d.time + S),
      (d.advanceCoordinates t).re ≤ d.front + 1 ∧ |(d.advanceCoordinates t).im| ≤ ε) ∧
    ∀ t : ℝ≥0, t < d.time + S → (d.advanceCoordinates t).re < d.front + 1 := by
  let p := longitudinalCoordinate d.chart closedRibbon d.front
  let η := fun t => d.trace (d.time + t)
  have hi := lower_lipschitz_injOn d.stepChart ribbonStepCompact L d.step_lower
  have hmap : MapsTo η (Icc 0 S) (d.stepChart '' ribbonStepCompact) := by
    intro t ht
    exact image_mono inter_subset_left (hpath ht)
  have hη : Continuous η := d.witness.1.comp (continuous_const.add continuous_id)
  have hq : ContinuousOn d.futureCoordinates (Icc 0 S) :=
    continuousOn_const.add ((coordinateInverse_lipschitz d.stepChart ribbonStepCompact L
      d.step_lower).continuousOn.comp hη.continuousOn hmap)
  have hqzero := d.futureCoordinates_zero hε
  have hpeq (t : ℝ≥0) (ht : t ∈ Icc 0 S) :
      p (η t) = (d.futureCoordinates t).re - d.front := by
    dsimp only [p]
    rw [d.global_progress_eq_step (hmap ht)]
    simp only [η, longitudinalCoordinate, RibbonHistory.futureCoordinates, Complex.add_re,
      Complex.ofReal_re, add_sub_cancel_left, sub_zero]
  have hp : ContinuousOn (fun t => p (η t)) (Icc 0 S) :=
    ((Complex.continuous_re.comp_continuousOn hq).sub continuousOn_const).congr
      (fun t ht => hpeq t ht)
  have hp0 : p (η 0) < 1 := by
    rw [hpeq 0 ⟨bot_le, bot_le⟩, hqzero, d.attained]
    simp
  have hprior := strict_before_attained_front _ 1 S hp hp0 hfirst
  have hqre : (d.futureCoordinates S).re = d.front + 1 := by
    have hh := (hpeq S ⟨bot_le, le_rfl⟩).symm.trans hhit
    linarith
  have hqcore (t : ℝ≥0) (ht : t ∈ Icc 0 S) :
      d.futureCoordinates t ∈ closedRibbon ∧ |(d.futureCoordinates t).im| ≤ ε := by
    obtain ⟨w, ⟨hwK, hwV⟩, he⟩ := hpath ht
    have hqw : d.futureCoordinates t = (d.front : ℂ) + w := by
      simp only [RibbonHistory.futureCoordinates, ← he, coordinateInverse_left hi hwK]
    rw [hqw]
    exact ⟨d.stepCompact_maps hwK, by
      simpa only [Complex.add_im, Complex.ofReal_im, zero_add] using hwV.2.2.1.le⟩
  have hqoffset : |(d.futureCoordinates S).im| ≤ ε / 4 := by
    have h1 : (1 : ℂ) ∈ ribbonStepCompact := by
      change -(1 / 2 : ℝ) ≤ 1 ∧ 1 ≤ 5 / 2 ∧ |(0 : ℝ)| ≤ 1 / 2
      norm_num
    have hd := d.step_lower _ (coordinateInverse_mem (hmap ⟨bot_le, le_rfl⟩)) 1 h1
    rw [coordinateInverse_right (hmap ⟨bot_le, le_rfl⟩)] at hd
    have habs : |(d.futureCoordinates S).im| ≤
        dist (coordinateInverse d.stepChart ribbonStepCompact (η S)) 1 := by
      simpa only [RibbonHistory.futureCoordinates, Complex.add_im, Complex.ofReal_im,
        zero_add, dist_eq_norm, Complex.sub_im, Complex.one_im, sub_zero] using
        Complex.abs_im_le_norm (coordinateInverse d.stepChart ribbonStepCompact (η S) - 1)
    have hnorm : dist (η S) (d.stepChart 1) < (ε / L) / 4 := by
      simpa only [dist_eq_norm, η, RibbonHistory.stepChart] using hoffset
    have hmul := mul_lt_mul_of_pos_left hnorm (show 0 < (L : ℝ) from hL)
    have he : (L : ℝ) * ((ε / L) / 4) = ε / 4 := by field_simp
    exact (habs.trans hd).trans (he ▸ hmul.le)
  have hsub (t : ℝ≥0) (ht : t ∈ Icc 0 (d.time + S)) : t - d.time ∈ Icc 0 S :=
    ⟨bot_le, (tsub_le_iff_right).mpr (by simpa only [add_comm] using ht.2)⟩
  have hleft : ContinuousOn (fun t => d.coordinates (min t d.time))
      (Icc 0 (d.time + S)) := d.coordinates_continuous.comp
        (continuous_id.min continuous_const).continuousOn (fun _ _ => ⟨bot_le, min_le_right _ _⟩)
  have hright : ContinuousOn (fun t => d.futureCoordinates (t - d.time))
      (Icc 0 (d.time + S)) := hq.comp
        (continuous_id.sub continuous_const).continuousOn hsub
  have hcont : ContinuousOn d.advanceCoordinates (Icc 0 (d.time + S)) := by
    unfold RibbonHistory.advanceCoordinates
    apply ContinuousOn.if ?_ (hleft.mono inter_subset_left) (hright.mono inter_subset_left)
    intro t ht
    have htT : t = d.time := by
      have hf : t ∈ frontier (Iic d.time) := ht.2
      simpa only [frontier_Iic, mem_singleton_iff] using hf
    simp only [htT, min_self, tsub_self, hqzero]
  have hold (t : ℝ≥0) (ht : t ≤ d.time) : d.advanceCoordinates t = d.coordinates t := by
    simp only [RibbonHistory.advanceCoordinates, ite_eq_left ht, min_eq_left ht]
  have hnew (t : ℝ≥0) (ht : d.time < t) :
      d.advanceCoordinates t = d.futureCoordinates (t - d.time) := by
    simp only [RibbonHistory.advanceCoordinates, ite_eq_right (not_le_of_gt ht)]
  have hTS : d.time < d.time + S := lt_add_of_pos_right _ hS
  refine ⟨hcont, ?_, ?_, ?_, hqoffset, ?_, ?_, ?_⟩
  · intro t ht
    by_cases htT : t ≤ d.time
    · rw [Function.comp_apply, hold t htT]
      exact d.trace_coordinates ⟨bot_le, htT⟩
    · rw [Function.comp_apply, hnew t (lt_of_not_ge htT), RibbonHistory.futureCoordinates]
      change d.trace t = d.stepChart (coordinateInverse d.stepChart ribbonStepCompact
        (η (t - d.time)))
      rw [coordinateInverse_right (hmap (hsub t ht))]
      simp only [η, add_tsub_cancel_of_le (le_of_not_ge htT)]
  · rw [hold 0 bot_le]
    exact d.initial_front
  · rw [hnew _ hTS, add_tsub_cancel_left]
    apply Complex.ext <;> simp [hqre]
  · intro t ht
    by_cases htT : t ≤ d.time
    · rw [hold t htT]
      exact d.coordinates_ribbon ⟨bot_le, htT⟩
    · rw [hnew t (lt_of_not_ge htT)]
      exact (hqcore _ (hsub t ht)).1
  · intro t ht
    by_cases htT : t ≤ d.time
    · rw [hold t htT]
      obtain ⟨hr, hi⟩ := d.past_core t ⟨bot_le, htT⟩
      exact ⟨by linarith, hi⟩
    · rw [hnew t (lt_of_not_ge htT)]
      refine ⟨?_, (hqcore _ (hsub t ht)).2⟩
      rcases (hsub t ht).2.eq_or_lt with he | hlt
      · rw [he, hqre]
      · have hh := hprior _ hlt
        rw [hpeq _ (hsub t ht)] at hh
        linarith
  · intro t ht
    by_cases htT : t ≤ d.time
    · rw [hold t htT]
      linarith [(d.past_core t ⟨bot_le, htT⟩).1]
    · rw [hnew t (lt_of_not_ge htT)]
      have hlt : t - d.time < S := by
        exact (tsub_lt_iff_left (le_of_not_ge htT)).mpr (by simpa only [add_comm] using ht)
      have hh := hprior _ hlt
      rw [hpeq _ ⟨bot_le, hlt.le⟩] at hh
      linarith

/-- A successful full step produces the actual history at the next
integer front, with the same driver, trace, and Loewner maps. The only
new geometric data are the deterministic bounds on the next patch. -/
theorem RibbonHistory.next_history_of_stepEvent
    {C L : ℝ≥0} {ε : ℝ} (d : RibbonHistory C L ε)
    (hε : ε ≤ 1 / 8) (hL : 0 < L) (κ v c : ℝ)
    (hstep : d.futureTrace ∈ d.stepEvent κ v c)
    (hupper : LipschitzOnWith C d.chart (ribbonStepPatch (d.front + 1)))
    (hlower : ∀ u ∈ ribbonStepPatch (d.front + 1),
      ∀ v ∈ ribbonStepPatch (d.front + 1), dist u v ≤ L * dist (d.chart u) (d.chart v)) :
    ∃ d' : RibbonHistory C L ε,
      d'.front = d.front + 1 ∧
      d'.time = d.time + frontTime
        (fun t => longitudinalCoordinate d.chart closedRibbon d.front (d.futureTrace t)) 1 ∧
      d'.chart = d.chart ∧ d'.U = d.U ∧ d'.trace = d.trace ∧
      d'.forward = d.forward ∧ d'.inverse = d.inverse ∧
      d'.coordinates = d.advanceCoordinates := by
  let S := frontTime
    (fun t => longitudinalCoordinate d.chart closedRibbon d.front (d.futureTrace t)) 1
  obtain ⟨hfirst, hhit, hS, hpath, hoffset⟩ := hstep.1
  obtain ⟨hcont, htrace, hzero, hattain, hoff, hribbon, hcore, hstrict⟩ :=
    d.successful_continuation hε hL S hfirst hhit hS hpath hoffset
  let d' : RibbonHistory C L ε := {
    U := d.U
    trace := d.trace
    forward := d.forward
    inverse := d.inverse
    driver_continuous := d.driver_continuous
    witness := d.witness
    chart := d.chart
    chart_continuous := d.chart_continuous
    chart_injective := d.chart_injective
    chart_upper := d.chart_upper
    chart_escape := d.chart_escape
    front := d.front + 1
    offset := (d.futureCoordinates S).im
    front_ge_one := by linarith [d.front_ge_one]
    offset_bound := hoff
    patch_upper := hupper
    patch_lower := hlower
    time := d.time + S
    time_pos := d.time_pos.trans_le (le_add_of_nonneg_right bot_le)
    coordinates := d.advanceCoordinates
    coordinates_continuous := hcont
    trace_coordinates := htrace
    initial_front := hzero
    attained := hattain
    coordinates_ribbon := hribbon
    past_core := hcore
    strict_past := hstrict }
  exact ⟨d', rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end SLEExactGauge

end

end OAI
