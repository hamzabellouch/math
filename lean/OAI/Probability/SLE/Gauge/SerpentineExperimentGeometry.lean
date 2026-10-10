import OAI.Probability.SLE.Gauge.SerpentineFittedShadow
import OAI.Probability.SLE.Gauge.SerpentineReflection
import OAI.Probability.SLE.Gauge.ProperRibbonCoordinates

namespace OAI

/-! The actual left-or-right displaced serpentine. Reflection is applied
to both the physical image and the normal coordinate, so the initial chart
is still `z ↦ I*z`. -/

noncomputable section
open Set Filter Metric ComplexConjugate
open scoped NNReal

namespace SLEExactGauge.Serpentine
open RibbonCoordinates

def experimentChart (s : ℝ) (w : ℂ) (m : ℕ) : ℂ → ℂ :=
  if 0 ≤ w.re then fitChart s w m else reflectedChart (fitChart s w m)

def experimentSpine (s : ℝ) (w : ℂ) (m : ℕ) (t : ℝ) : ℂ :=
  if 0 ≤ w.re then fitSpine s w m t else loewnerMirror (fitSpine s w m t)

def physicalExperimentChart (s : ℝ) (w : ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  if 0 ≤ w.re then physicalFitChart s w m z else loewnerMirror (physicalFitChart s w m (conj z))

lemma loewnerMirror_real_mul (c : ℝ) (z : ℂ) :
    loewnerMirror ((c : ℂ) * z) = (c : ℂ) * loewnerMirror z := by
  simp [loewnerMirror, mul_neg]

lemma physicalExperimentChart_eq (s : ℝ) (w : ℂ) (m : ℕ) (z : ℂ) :
    physicalExperimentChart s w m z = (ribbonWidth (halfHeight s) m : ℂ) * experimentChart s w m z := by
  by_cases hw : 0 ≤ w.re
  · simp only [physicalExperimentChart, experimentChart, ite_eq_left hw, physicalFitChart]
  · simp only [physicalExperimentChart, experimentChart, ite_eq_right hw, physicalFitChart,
      reflectedChart, loewnerMirror_real_mul]

theorem experimentChart_geometry {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m : ℕ} (hm : 0 < m) :
    Continuous (experimentChart s w m) ∧ InjOn (experimentChart s w m) closedRibbon ∧
    (∀ k : ℝ, LipschitzOnWith 2 (experimentChart s w m) (ribbonStepPatch k) ∧
      ∀ z ∈ ribbonStepPatch k, ∀ z' ∈ ribbonStepPatch k,
        dist z z' ≤ 2 * dist (experimentChart s w m z) (experimentChart s w m z')) ∧
    (∀ z ∈ closedRibbon, 0 < z.re → experimentChart s w m z ∈ upperHalfPlane) ∧
    (∀ z ∈ closedRibbon, z.re ≤ 4 → experimentChart s w m z = Complex.I * z) := by
  have hcont := fitChart_continuous hs w hw hm
  have hinj := fitChart_injective hs w hw hm
  have hpatch := fitChart_patch_bounds hs w hw hm
  have hu := fitChart_upper hs w hw hm
  have hi : ∀ z ∈ closedRibbon, z.re ≤ 4 → fitChart s w m z = Complex.I * z := by
    intro z _ hz
    exact fitChart_initial hs w hw hm (hz.trans (fit_parameters hs w hw hm).2.2.2)
  by_cases hwr : 0 ≤ w.re
  · simpa only [experimentChart, ite_eq_left hwr] using ⟨hcont, hinj, hpatch, hu, hi⟩
  · simp only [experimentChart, ite_eq_right hwr]
    exact ⟨reflectedChart_continuous hcont, reflectedChart_injective hinj,
      fun k => ⟨reflectedChart_patch_upper (hpatch k).1,
        reflectedChart_patch_lower (hpatch k).2⟩,
      reflectedChart_upper hu, reflectedChart_initial hi⟩

lemma experimentChart_width (s : ℝ) (w : ℂ) (m : ℕ) {z : ℂ} (hz : z ∈ closedRibbon) :
    ‖experimentChart s w m z - experimentSpine s w m z.re‖ ≤ 1 := by
  by_cases hwr : 0 ≤ w.re
  · simpa only [experimentChart, experimentSpine, ite_eq_left hwr] using fitChart_width s w m hz
  · simpa only [experimentChart, experimentSpine, ite_eq_right hwr] using
      reflectedChart_width (P := fitChart s w m) (σ := fitSpine s w m)
        (fun _ hz => fitChart_width s w m hz) z hz

lemma experimentSpine_eventually_ray (s : ℝ) (w : ℂ) (m : ℕ) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      experimentSpine s w m t = experimentSpine s w m T + ((t - T : ℝ) : ℂ) * Complex.I := by
  obtain ⟨T, hT, htail⟩ := fitSpine_eventually_ray s w m
  refine ⟨T, hT, fun t ht => ?_⟩
  by_cases hwr : 0 ≤ w.re
  · simpa only [experimentSpine, ite_eq_left hwr] using htail t ht
  · simp only [experimentSpine, ite_eq_right hwr]
    rw [htail t ht]
    simp [loewnerMirror, mul_neg, add_comm]

lemma experimentChart_real_norm (s : ℝ) (w : ℂ) (m : ℕ) (t : ℝ) :
    ‖experimentChart s w m (t : ℂ)‖ = ‖fitSpine s w m t‖ := by
  by_cases hwr : 0 ≤ w.re <;>
    simp [experimentChart, hwr, reflectedChart, fitChart, normalRibbon]

theorem experimentChart_escape (s : ℝ) (w : ℂ) (m : ℕ) :
    Tendsto (fun t : ℝ => ‖experimentChart s w m (t : ℂ)‖) atTop atTop := by
  simp only [experimentChart_real_norm]
  exact tendsto_norm_cocompact_atTop.comp
    (completeSpine_escape m (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m))

theorem experimentChart_zero {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m : ℕ} (hm : 0 < m) : experimentChart s w m 0 = 0 := by
  have hh := (experimentChart_geometry hs w hw hm).2.2.2.2 0
    (by simp [closedRibbon]) (by norm_num)
  simpa only [mul_zero] using hh

theorem experimentChart_closedEmbedding {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m : ℕ} (hm : 0 < m) :
    Topology.IsClosedEmbedding (fun z : closedRibbon => experimentChart s w m z) := by
  obtain ⟨hc, hi, _⟩ := experimentChart_geometry hs w hw hm
  obtain ⟨T, hT, htail⟩ := experimentSpine_eventually_ray s w m
  exact ribbon_closedEmbedding_of_linear_tail _ hc.continuousOn hi _ T hT
    (experimentSpine s w m T) htail (fun _ hz => experimentChart_width s w m hz)

theorem experimentChart_global_progress {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m : ℕ} (hm : 0 < m) :
    ∃ g : C(ℂ, ℝ), ∀ z ∈ closedRibbon, g (experimentChart s w m z) = z.re :=
  exists_global_ribbon_progress _ (experimentChart_closedEmbedding hs w hw hm)

lemma reflected_positiveCenter {s : ℝ} {w : ℂ} (hw : w.re < 0) :
    loewnerMirror (positiveCenter s w) = center s w := by
  have hn : ¬ 0 ≤ w.re := not_le.mpr hw
  apply Complex.ext
  · simp only [loewnerMirror_re, positiveCenter, center, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    rw [abs_of_neg hw]
    simp only [displacementSign, ite_eq_right hn]
    ring
  · simp only [loewnerMirror_im, positiveCenter, center, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, add_zero, zero_add]

theorem physicalExperimentChart_retained_disk {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m j i : ℕ} (hm : 0 < m) (hj : j < m) (hi : i < m) {z : ℂ}
    (hz : z.re ∈ Icc
      ((retainedStep (connectorEntry (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m)) m j i : ℝ) + 1 / 3)
      ((retainedStep (connectorEntry (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m)) m j i : ℝ) + 2 / 3))
    (ha : |z.im| ≤ 1) :
    physicalExperimentChart s w m z ∈ closedBall (center s w) (s / 20) := by
  by_cases hwr : 0 ≤ w.re
  · simpa only [physicalExperimentChart, ite_eq_left hwr] using
      physicalFitChart_retained_disk hs w hw hwr hm hj hi hz ha
  · have hzc : (conj z).re ∈ Icc
        ((retainedStep (connectorEntry (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m)) m j i : ℝ) + 1 / 3)
        ((retainedStep (connectorEntry (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m)) m j i : ℝ) + 2 / 3) := by
      simpa only [Complex.conj_re] using hz
    have hac : |(conj z).im| ≤ 1 := by simpa only [Complex.conj_im, abs_neg] using ha
    have hd := physicalFitChart_retained_distance hs w hw hm hj hi hzc hac
    change dist _ _ ≤ _
    rw [physicalExperimentChart, ite_eq_right hwr, ← reflected_positiveCenter (lt_of_not_ge hwr),
      loewnerMirror_dist]
    linarith

theorem physicalExperimentChart_avoids_shadow {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m : ℕ} (hm : 0 < m) {z : ℂ} (ha : |z.im| ≤ 1) :
    ¬ (|(physicalExperimentChart s w m z).re - w.re| < s / 100 ∧
      w.im - s / 100 < (physicalExperimentChart s w m z).im) := by
  by_cases hwr : 0 ≤ w.re
  · simpa only [physicalExperimentChart, ite_eq_left hwr, abs_of_nonneg hwr] using
      physicalFitChart_avoids_shadow hs w hw hm ha
  · have hneg : w.re < 0 := lt_of_not_ge hwr
    have hac : |(conj z).im| ≤ 1 := by simpa only [Complex.conj_im, abs_neg] using ha
    have hn := physicalFitChart_avoids_shadow hs w hw hm hac
    have he : abs (-(physicalFitChart s w m (conj z)).re - w.re) =
        abs ((physicalFitChart s w m (conj z)).re - |w.re|) := by
      rw [abs_of_neg hneg]
      have hh : -(physicalFitChart s w m (conj z)).re - w.re =
          -((physicalFitChart s w m (conj z)).re - -w.re) := by ring
      rw [hh, abs_neg]
    simpa only [physicalExperimentChart, ite_eq_right hwr, loewnerMirror_re, loewnerMirror_im, he] using hn

theorem selected_middle_regions_inside {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m : ℕ} (hm : 0 < m) {ε : ℝ} (hε : ε ≤ 1) :
    ∀ k ∈ retainedSteps (connectorEntry (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m)) m,
      physicalMiddleRegion (physicalExperimentChart s w m) closedRibbon k ε ⊆
        closedBall (center s w) (s / 20) := by
  intro k hk
  obtain ⟨⟨j, i⟩, _, rfl⟩ := Finset.mem_image.mp hk
  rw [physicalMiddleRegion_eq_image_middleStrip _ (Nat.cast_nonneg _) hε]
  rintro y ⟨z, hz, rfl⟩
  exact physicalExperimentChart_retained_disk hs w hw hm j.isLt i.isLt
    ⟨by linarith [hz.1], by linarith [hz.2.1]⟩ (hz.2.2.le.trans hε)

end SLEExactGauge.Serpentine

end

end OAI
