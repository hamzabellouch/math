import OAI.Probability.SLE.Geometry.FirstHeightSupport
import OAI.Probability.SLE.Gauge.RibbonGoodPrefix
import OAI.Probability.SLE.Gauge.SerpentineExperimentGeometry

namespace OAI

/-! A single vertical support event starts every fitted serpentine at
integer front one. Its probability is independent of the marked point
and of the multiplicity. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal unitInterval

namespace SLEExactGauge.Serpentine
open RibbonCoordinates FirstFrontPassage FirstHeightSupport

def initialRiseStrip (ε : ℝ) : Set ℂ := {z | |z.re| < ε / 4}

def initialRiseTarget : Set ℂ := {z | 1 < z.im}

def InitialRise {Ω : Type*} (γ : Ω → ℝ≥0 → ℂ) (ε : ℝ) : Set Ω :=
  {ω | ∃ T : ℝ≥0, 0 < T ∧ MapsTo (γ ω) (Icc 0 T) (initialRiseStrip ε) ∧
    γ ω T ∈ initialRiseTarget}

lemma initialRise_positive {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ : Ω → ℝ≥0 → ℂ) (hsupport : PublishedGeometricTubeSupport P γ)
    {ε : ℝ} (hε : 0 < ε) : 0 < P (InitialRise γ ε) := by
  apply hsupport _ (verticalPath 4) (verticalPath_injective (by norm_num))
  · intro t ht
    change 0 < (verticalPath 4 t).im
    simp only [verticalPath_apply, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero]
    have ht0 : 0 < (t : ℝ) := by
      by_contra hn
      exact ht (Subtype.ext (le_antisymm (le_of_not_gt hn) t.property.1))
    linarith
  · exact isOpen_lt Complex.continuous_re.abs continuous_const
  · exact isOpen_lt continuous_const Complex.continuous_im
  · rintro z ⟨t, rfl⟩
    change |(verticalPath 4 t).re| < ε / 4
    simpa only [verticalPath_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, abs_zero] using
      (show (0 : ℝ) < ε / 4 by positivity)
  · change 1 < (((4 / 2 : ℝ) : ℂ) * Complex.I).im
    norm_num

lemma initial_prefix_coordinates (γ : ℝ≥0 → ℂ) (P : ℂ → ℂ)
    {ε : ℝ} (hε : ε ≤ 1)
    (hP : ∀ z ∈ closedRibbon, z.re ≤ 4 → P z = Complex.I * z)
    {t : ℝ≥0} (hheight : 0 ≤ (γ t).im ∧ (γ t).im ≤ 1)
    (hstrip : |(γ t).re| < ε / 4) :
    ∃ z ∈ closedRibbon, |z.im| ≤ ε / 4 ∧ z.re = (γ t).im ∧ P z = γ t := by
  let z := -Complex.I * γ t
  have hzre : z.re = (γ t).im := by simp [z]
  have hzim : z.im = -(γ t).re := by simp [z]
  have hz : z ∈ closedRibbon := by
    change 0 ≤ z.re ∧ |z.im| ≤ 1
    rw [hzre, hzim, abs_neg]
    exact ⟨hheight.1, by linarith⟩
  refine ⟨z, hz, ?_, hzre, ?_⟩
  · rw [hzim, abs_neg]
    exact hstrip.le
  · rw [hP z hz (by rw [hzre]; linarith)]
    dsimp [z]
    rw [← mul_assoc]
    norm_num

theorem initialRise_gives_goodPrefix
    (γ : ℝ≥0 → ℂ) (hγ : Continuous γ) (hγ0 : γ 0 = 0)
    (hγH : ∀ t, 0 ≤ (γ t).im)
    (P : ℂ → ℂ) (g : C(ℂ, ℝ)) (hg : ∀ z ∈ closedRibbon, g (P z) = z.re)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hP : ∀ z ∈ closedRibbon, z.re ≤ 4 → P z = Complex.I * z)
    (hrise : () ∈ InitialRise (fun _ : Unit => γ) ε) :
    () ∈ GoodRibbonPrefix (fun _ : Unit => γ)
      (fun _ => firstFrontTime (fun t => g (γ t)) 1) P ε := by
  obtain ⟨T, _, hstrip, htarget⟩ := hrise
  obtain ⟨τ, _, _, hτT, hhit, hprior⟩ :=
    exists_first_height γ hγ hγ0 zero_lt_one htarget
  have hheight (t : ℝ≥0) (ht : t ≤ τ) : 0 ≤ (γ t).im ∧ (γ t).im ≤ 1 := by
    refine ⟨hγH t, ?_⟩
    rcases eq_or_lt_of_le ht with rfl | ht
    · exact hhit.le
    · exact (hprior t ht).le
  have hcoord (t : ℝ≥0) (ht : t ≤ τ) := initial_prefix_coordinates γ P hε1 hP
    (hheight t ht) (hstrip ⟨bot_le, ht.trans hτT.le⟩)
  have hgheight (t : ℝ≥0) (ht : t ≤ τ) : g (γ t) = (γ t).im := by
    obtain ⟨z, hz, _, hzre, he⟩ := hcoord t ht
    exact (congrArg g he.symm).trans ((hg z hz).trans hzre)
  have hleast : IsLeast {t : ℝ≥0 | 0 ≤ t ∧ g (γ t) - 1 ∈ ({0} : Set ℝ)} τ := by
    refine ⟨⟨bot_le, ?_⟩, ?_⟩
    · simp only [hgheight τ le_rfl, hhit, sub_self, mem_singleton_iff]
    · intro t ht
      by_contra hn
      have htτ : t < τ := lt_of_not_ge hn
      have he : g (γ t) = 1 := sub_eq_zero.mp ht.2
      rw [hgheight t htτ.le] at he
      exact (ne_of_lt (hprior t htτ)) he
  have hfront : firstFrontTime (fun t => g (γ t)) 1 = (τ : WithTop ℝ≥0) := by
    unfold firstFrontTime hittingAfter
    rw [ite_eq_left ⟨τ, hleast.1⟩, hleast.csInf_eq]
  change firstFrontTime (fun t => g (γ t)) 1 ≠ ⊤ ∧ _
  rw [hfront]
  refine ⟨WithTop.coe_ne_top, ?_, ?_⟩
  · intro t ht
    obtain ⟨z, hz, hzi, _, he⟩ := hcoord t ht.2
    exact ⟨z, ⟨hz, hzi.trans (by linarith)⟩, he⟩
  · obtain ⟨z, hz, hzi, _, he⟩ := hcoord τ le_rfl
    exact ⟨z, ⟨hz, hzi⟩, he⟩

/-- The same positive lower bound works for every chart which is the
initial vertical strip, and for every global extension of its progress. -/
theorem uniform_initial_goodPrefix_probability
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ μ)
    (hsupport : PublishedGeometricTubeSupport μ γ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ P : ℂ → ℂ, ∀ g : C(ℂ, ℝ),
      (∀ z ∈ closedRibbon, g (P z) = z.re) →
      (∀ z ∈ closedRibbon, z.re ≤ 4 → P z = Complex.I * z) →
      q ≤ μ (GoodRibbonPrefix γ (ribbonFrontStop g γ 1) P ε) := by
  refine ⟨μ (InitialRise γ ε), initialRise_positive μ γ hsupport hε, ?_⟩
  intro P g hg hP
  apply measure_mono_ae
  obtain ⟨_, _, htrace⟩ := hSLE.2
  filter_upwards [htrace] with ω hω
  intro hrise
  obtain ⟨G, F, hw⟩ := hω
  exact initialRise_gives_goodPrefix (γ ω) hw.1 hw.2.1 hw.2.2.1 P g hg hε hε1 hP hrise

theorem uniform_experiment_initial_goodPrefix_probability
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ μ)
    (hsupport : PublishedGeometricTubeSupport μ γ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ s : ℝ, 0 < s → ∀ w : ℂ, s ≤ w.im →
      ∀ m : ℕ, 0 < m → ∀ g : C(ℂ, ℝ),
        (∀ z ∈ closedRibbon, g (experimentChart s w m z) = z.re) →
        q ≤ μ (GoodRibbonPrefix γ (ribbonFrontStop g γ 1) (experimentChart s w m) ε) := by
  obtain ⟨q, hq, hp⟩ := uniform_initial_goodPrefix_probability μ κ γ hSLE hsupport hε hε1
  refine ⟨q, hq, fun s hs w hw m hm g hg => ?_⟩
  exact hp _ g hg (experimentChart_geometry hs w hw hm).2.2.2.2

end SLEExactGauge.Serpentine

end

end OAI
