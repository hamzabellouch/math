import OAI.Probability.InvariantIsing.Spectral.FiniteSpectralContinuity

namespace OAI

/-! The resolvent and the edge-capped inverse for a general spectral law.
The upper edge is an explicit parameter; the hypotheses below say that the
law is supported below it. No inverse is assumed to exist at the edge. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology Classical

namespace InvariantIsing

def measureResolvent (μ : Measure ℝ) (b : ℝ) : ℝ := ∫ y, 1 / (b - y) ∂μ

def measureInverse (μ : Measure ℝ) (e x : ℝ) : ℝ :=
  if h : ∃ b, e < b ∧ measureResolvent μ b = x then h.choose else e

def measureR (μ : Measure ℝ) (e x : ℝ) : ℝ :=
  if 0 < x then measureInverse μ e x - 1 / x else ∫ y, y ∂μ

lemma measurable_resolventKernel (b : ℝ) : Measurable (fun y : ℝ => 1 / (b - y)) :=
  measurable_const.div (measurable_const.sub measurable_id)

lemma resolventKernel_bound {e b y : ℝ} (hb : e < b) (hy : y ≤ e) :
    ‖1 / (b - y)‖ ≤ 1 / (b - e) := by
  rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (by linarith))]
  exact one_div_le_one_div_of_le (sub_pos.mpr hb) (by linarith)

lemma integrable_resolventKernel (μ : Measure ℝ) [IsFiniteMeasure μ]
    {e b : ℝ} (hμ : ∀ᵐ y ∂μ, y ≤ e) (hb : e < b) :
    Integrable (fun y => 1 / (b - y)) μ := by
  apply (integrable_const (1 / (b - e))).mono' (measurable_resolventKernel b).aestronglyMeasurable
  filter_upwards [hμ] with y hy
  exact resolventKernel_bound hb hy

lemma measureResolvent_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {e b : ℝ} (hμ : ∀ᵐ y ∂μ, y ≤ e) (hb : e < b) :
    measureResolvent μ b ≤ 1 / (b - e) := by
  have hi := integral_mono_ae (integrable_resolventKernel μ hμ hb)
    (integrable_const (1 / (b - e))) (hμ.mono fun y hy =>
      one_div_le_one_div_of_le (sub_pos.mpr hb) (by linarith))
  simpa only [measureResolvent, integral_const, probReal_univ, one_smul] using hi

lemma le_measureResolvent (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {l e b : ℝ} (hμ : ∀ᵐ y ∂μ, y ∈ Icc l e) (hb : e < b) :
    1 / (b - l) ≤ measureResolvent μ b := by
  have hex := hμ.exists
  have hbl : l < b := by obtain ⟨y, hy⟩ := hex; linarith [hy.1, hy.2]
  have hi := integral_mono_ae (integrable_const (1 / (b - l)))
    (integrable_resolventKernel μ (hμ.mono fun _ h => h.2) hb)
    (hμ.mono fun y hy => one_div_le_one_div_of_le (by linarith [hy.2]) (by linarith [hy.1]))
  simpa only [measureResolvent, integral_const, probReal_univ, one_smul] using hi

theorem measureResolvent_strictAnti (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {e b c : ℝ} (hμ : ∀ᵐ y ∂μ, y ≤ e) (hb : e < b) (hbc : b < c) :
    measureResolvent μ c < measureResolvent μ b := by
  have hi := integrable_resolventKernel μ hμ hb
  have hj := integrable_resolventKernel μ hμ (hb.trans hbc)
  have hlt : ∀ᵐ y ∂μ, 1 / (c - y) < 1 / (b - y) := hμ.mono fun y hy =>
    one_div_lt_one_div_of_lt (by linarith) (by linarith)
  have hle := integral_mono_ae hj hi (hlt.mono fun _ h => h.le)
  apply lt_of_le_of_ne hle
  intro heq
  have hae := (integral_eq_iff_of_ae_le hj hi (hlt.mono fun _ h => h.le)).mp heq
  obtain ⟨y, hy, he⟩ := (hlt.and hae).exists
  exact (ne_of_lt hy) he

theorem continuousAt_measureResolvent (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {e b : ℝ} (hμ : ∀ᵐ y ∂μ, y ≤ e) (hb : e < b) :
    ContinuousAt (measureResolvent μ) b := by
  let c := (e + b) / 2
  have hce : e < c := by dsimp only [c]; linarith
  have hcb : c < b := by dsimp only [c]; linarith
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => 1 / (c - e))
  · exact Eventually.of_forall fun z => (measurable_resolventKernel z).aestronglyMeasurable
  · filter_upwards [Ioi_mem_nhds hcb] with z hz
    have hz' : c < z := hz
    filter_upwards [hμ] with y hy
    exact (resolventKernel_bound (hce.trans hz') hy).trans
      (one_div_le_one_div_of_le (sub_pos.mpr hce) (by linarith))
  · exact integrable_const _
  · filter_upwards [hμ] with y hy
    exact (continuousAt_const.div (continuousAt_id.sub_const y)
      (by change b - y ≠ 0; linarith)).tendsto

theorem exists_measureResolvent_solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {e lo x : ℝ} (hμ : ∀ᵐ y ∂μ, y ≤ e) (hlo : e < lo)
    (hx : 0 < x) (hloValue : x ≤ measureResolvent μ lo) :
    ∃ b, e < b ∧ measureResolvent μ b = x := by
  let hi := lo + 1 / x
  have hhi : lo < hi := by dsimp only [hi]; linarith [one_div_pos.mpr hx]
  have hhiValue : measureResolvent μ hi ≤ x := by
    apply (measureResolvent_le μ hμ (hlo.trans hhi)).trans
    have hd : 1 / x ≤ hi - e := by dsimp only [hi]; linarith
    simpa using one_div_le_one_div_of_le (one_div_pos.mpr hx) hd
  have hc : ContinuousOn (measureResolvent μ) (Icc lo hi) := fun b hb =>
    (continuousAt_measureResolvent μ hμ (hlo.trans_le hb.1)).continuousWithinAt
  obtain ⟨b, hb, hv⟩ := intermediate_value_Icc' hhi.le hc ⟨hhiValue, hloValue⟩
  exact ⟨b, hlo.trans_le hb.1, hv⟩

theorem measureInverse_eq_of_solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {e b x : ℝ} (hμ : ∀ᵐ y ∂μ, y ≤ e) (hb : e < b)
    (hsol : measureResolvent μ b = x) : measureInverse μ e x = b := by
  have hex : ∃ b, e < b ∧ measureResolvent μ b = x := ⟨b, hb, hsol⟩
  rw [measureInverse, dite_eq_left hex]
  have hs := hex.choose_spec
  rcases lt_trichotomy hex.choose b with h | h | h
  · have := measureResolvent_strictAnti μ hμ hs.1 h
    linarith [hs.2]
  · exact h
  · have := measureResolvent_strictAnti μ hμ hb h
    linarith [hs.2]

theorem measureInverse_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {e x : ℝ} (hμ : ∀ᵐ y ∂μ, y ≤ e) (hx : 0 < x) :
    e ≤ measureInverse μ e x ∧ measureInverse μ e x ≤ e + 1 / x := by
  by_cases hex : ∃ b, e < b ∧ measureResolvent μ b = x
  · rw [measureInverse, dite_eq_left hex]
    have hs := hex.choose_spec
    refine ⟨hs.1.le, ?_⟩
    have hu := measureResolvent_le μ hμ hs.1
    rw [hs.2] at hu
    have hm := (le_div_iff₀ (sub_pos.mpr hs.1)).mp hu
    have hd : hex.choose - e ≤ 1 / x := (le_div_iff₀ hx).mpr (by nlinarith)
    linarith
  · simp only [measureInverse, dite_eq_right hex, le_refl, true_and]
    linarith [one_div_pos.mpr hx]

theorem measureR_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {l e x : ℝ} (hμ : ∀ᵐ y ∂μ, y ∈ Icc l e) (hx : 0 < x) :
    l ≤ measureR μ e x ∧ measureR μ e x ≤ e := by
  have hu := measureInverse_bounds μ (hμ.mono fun _ h => h.2) hx
  rw [measureR, ite_eq_left hx]
  refine ⟨?_, by linarith [hu.2]⟩
  by_cases hex : ∃ b, e < b ∧ measureResolvent μ b = x
  · rw [measureInverse, dite_eq_left hex]
    have hs := hex.choose_spec
    have hl := le_measureResolvent μ hμ hs.1
    rw [hs.2] at hl
    obtain ⟨y, hy⟩ := hμ.exists
    have hbl : 0 < hex.choose - l := by linarith [hy.1, hy.2, hs.1]
    have hm := (div_le_iff₀ hbl).mp hl
    have hd : 1 / x ≤ hex.choose - l := (div_le_iff₀ hx).mpr (by nlinarith)
    linarith
  · rw [measureInverse, dite_eq_right hex]
    by_contra hbad
    have hb : e < l + 1 / x := by linarith
    have hl := le_measureResolvent μ hμ hb
    have hv : x ≤ measureResolvent μ (l + 1 / x) := by simpa using hl
    exact hex (exists_measureResolvent_solution μ (hμ.mono fun _ h => h.2) hb hx hv)

end InvariantIsing

end

end OAI
