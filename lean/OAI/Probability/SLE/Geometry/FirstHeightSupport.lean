import OAI.Probability.SLE.Geometry.GeometricTubeSupport
import OAI.Probability.SLE.Gauge.RibbonSurvival
import OAI.Probability.SLE.RadiusClocks

namespace OAI

/-!
Positive probability of a narrow first-height crossing. The deterministic
first crossing is finite, positive, fresh, and its entire past lies in the
initial rectangle. A vertical supported path supplies the positive-probability
event at each fixed spatial scale.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal unitInterval

namespace SLEExactGauge.FirstHeightSupport

/-- The first capacity time at which the trace reaches the specified height. -/
def firstHeightTime (γ : ℝ≥0 → ℂ) (h : ℝ) : WithTop ℝ≥0 :=
  hittingAfter (fun t (_ : Unit) => (γ t).im - h) {0} 0 ()

/-- The actual first-height time is a stopping time for an adapted
continuous trace. -/
theorem firstHeightTime_isStoppingTime
    {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 m)
    (γ : Ω → ℝ≥0 → ℂ) (hγa : Adapted ℱ (fun t ω => γ ω t))
    (hγc : ∀ ω, Continuous (γ ω)) (h : ℝ) :
    IsStoppingTime ℱ (fun ω => firstHeightTime (γ ω) h) := by
  have hs := continuous_zero_hit_stopping ℱ (fun t ω => (γ ω t).im - h)
    (fun t => (Complex.continuous_im.measurable.comp (hγa t)).sub_const h)
    (fun ω => (Complex.continuous_im.comp (hγc ω)).sub continuous_const) 0
  change IsStoppingTime ℱ (hittingAfter (fun t ω => (γ ω t).im - h) {0} 0)
  exact hs

/-- A continuous trace which rises above a positive height has a genuine
first crossing. Every earlier point has strictly smaller height. -/
theorem exists_first_height
    (γ : ℝ≥0 → ℂ) (hγ : Continuous γ) (hγ0 : γ 0 = 0)
    {h : ℝ} (hh : 0 < h) {T : ℝ≥0} (hT : h < (γ T).im) :
    ∃ τ : ℝ≥0, firstHeightTime γ h = (τ : WithTop ℝ≥0) ∧ 0 < τ ∧ τ < T ∧
      (γ τ).im = h ∧ ∀ u : ℝ≥0, u < τ → (γ u).im < h := by
  have hcont : Continuous (fun t => (γ t).im) := Complex.continuous_im.comp hγ
  let K := Icc (0 : ℝ≥0) T ∩ (fun t => (γ t).im) ⁻¹' {h}
  have hK : IsCompact K := isCompact_Icc.inter_right
    (isClosed_singleton.preimage hcont)
  have hKn : K.Nonempty := by
    obtain ⟨t, ht, he⟩ := intermediate_value_Icc (show (0 : ℝ≥0) ≤ T from bot_le)
      hcont.continuousOn (show h ∈ Icc (γ 0).im (γ T).im by simpa [hγ0] using ⟨hh.le, hT.le⟩)
    exact ⟨t, ht, he⟩
  obtain ⟨τ, hτK, hmin⟩ := hK.exists_isLeast hKn
  have hhit : (γ τ).im = h := hτK.2
  have hτpos : 0 < τ := by
    by_contra hn
    have he : τ = 0 := le_antisymm (le_of_not_gt hn) bot_le
    rw [he, hγ0, Complex.zero_im] at hhit
    exact hh.ne' hhit.symm
  have hτT : τ < T := lt_of_le_of_ne hτK.1.2 (by
    intro he
    rw [he] at hhit
    exact (ne_of_gt hT) hhit)
  have hprior (u : ℝ≥0) (hu : u < τ) : (γ u).im < h := by
    by_contra hn
    have huT : u ≤ T := hu.le.trans hτK.1.2
    obtain ⟨v, hv, he⟩ := intermediate_value_Icc (show (0 : ℝ≥0) ≤ u from bot_le)
      hcont.continuousOn
      (show h ∈ Icc (γ 0).im (γ u).im by simpa [hγ0] using ⟨hh.le, le_of_not_gt hn⟩)
    have hvK : v ∈ K := ⟨⟨bot_le, hv.2.trans huT⟩, he⟩
    exact (not_le_of_gt hu) ((hmin hvK).trans hv.2)
  have hleast : IsLeast {t : ℝ≥0 | 0 ≤ t ∧ (γ t).im - h ∈ ({0} : Set ℝ)} τ := by
    refine ⟨⟨bot_le, by simp only [mem_singleton_iff, hhit, sub_self]⟩, ?_⟩
    intro t ht
    by_contra hn
    have hl := hprior t (lt_of_not_ge hn)
    have he : (γ t).im = h := sub_eq_zero.mp ht.2
    exact (ne_of_lt hl) he
  have htime : firstHeightTime γ h = (τ : WithTop ℝ≥0) := by
    unfold firstHeightTime hittingAfter
    rw [ite_eq_left ⟨τ, hleast.1⟩, hleast.csInf_eq]
  exact ⟨τ, htime, hτpos, hτT, hhit, hprior⟩

def narrowStrip (B : ℝ) : Set ℂ := {z | |z.re| < B / 16}

def aboveQuarterHeight (B : ℝ) : Set ℂ := {z | B / 4 < z.im}

/-- The measurable supported event used to obtain the narrow first crossing. -/
def narrowRiseEvent (B : ℝ) : Set C(ℝ≥0, ℂ) :=
  pathTubeEvent (narrowStrip B) (aboveQuarterHeight B)

theorem isOpen_narrowRiseEvent (B : ℝ) : IsOpen (narrowRiseEvent B) :=
  isOpen_pathTubeEvent (isOpen_lt Complex.continuous_re.abs continuous_const)
    (isOpen_lt continuous_const Complex.continuous_im)

local instance : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

theorem measurableSet_narrowRiseEvent (B : ℝ) : MeasurableSet (narrowRiseEvent B) :=
  (isOpen_narrowRiseEvent B).measurableSet

def NarrowFirstHeight (B : ℝ) (γ : ℝ≥0 → ℂ) : Prop :=
  ∃ τ : ℝ≥0, firstHeightTime γ (B / 4) = (τ : WithTop ℝ≥0) ∧ 0 < τ ∧
    (γ τ).im = B / 4 ∧ |(γ τ).re| < B / 16 ∧
    (∀ u : ℝ≥0, u < τ → (γ u).im < (γ τ).im) ∧
    γ '' Icc 0 τ ⊆ GuideSplice.closedInitialRectangle B

theorem narrowRiseEvent_gives_first_height
    {B : ℝ} (hB : 0 < B) (p : C(ℝ≥0, ℂ)) (hp0 : p 0 = 0)
    (hpH : ∀ t, 0 ≤ (p t).im) (hp : p ∈ narrowRiseEvent B) :
    NarrowFirstHeight B p := by
  obtain ⟨T, _, hstrip, habove⟩ := hp
  obtain ⟨τ, htime, hτ, hτT, hhit, hprior⟩ :=
    exists_first_height p p.continuous hp0 (by positivity : 0 < B / 4) habove
  have hτstrip : |(p τ).re| < B / 16 := hstrip ⟨bot_le, hτT.le⟩
  refine ⟨τ, htime, hτ, hhit, hτstrip, ?_, ?_⟩
  · intro u hu
    rw [hhit]
    exact hprior u hu
  · rintro z ⟨u, hu, rfl⟩
    refine ⟨(hstrip ⟨bot_le, hu.2.trans hτT.le⟩).le, hpH u, ?_⟩
    rcases eq_or_lt_of_le hu.2 with rfl | huτ
    · exact hhit.le
    · exact (hprior u huτ).le

/-- A vertical reference path for the fixed-scale support event. -/
def verticalPath (B : ℝ) : Path (0 : ℂ) (((B / 2 : ℝ) : ℂ) * Complex.I) where
  toFun t := (((t : ℝ) * (B / 2) : ℝ) : ℂ) * Complex.I
  continuous_toFun := (Complex.continuous_ofReal.comp
    (continuous_subtype_val.mul continuous_const)).mul continuous_const
  source' := by simp
  target' := by simp

@[simp] theorem verticalPath_apply (B : ℝ) (t : unitInterval) :
    verticalPath B t = (((t : ℝ) * (B / 2) : ℝ) : ℂ) * Complex.I := rfl

theorem verticalPath_injective {B : ℝ} (hB : 0 < B) : Function.Injective (verticalPath B) := by
  intro s t he
  have hi := congrArg Complex.im he
  simp only [verticalPath_apply, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero] at hi
  apply Subtype.ext
  nlinarith

theorem narrowRiseEvent_positive
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ : Ω → ℝ≥0 → ℂ) (hpublished : PublishedGeometricTubeSupport P γ)
    {B : ℝ} (hB : 0 < B) :
    0 < P {ω | ∃ T : ℝ≥0, 0 < T ∧ MapsTo (γ ω) (Icc 0 T) (narrowStrip B) ∧
      γ ω T ∈ aboveQuarterHeight B} := by
  apply hpublished _ (verticalPath B) (verticalPath_injective hB)
  · intro t ht
    change 0 < (verticalPath B t).im
    simp only [verticalPath_apply, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
    have ht0 : 0 < (t : ℝ) := by
      by_contra hn
      have he : (t : ℝ) = 0 := le_antisymm (le_of_not_gt hn) t.property.1
      exact ht (Subtype.ext he)
    exact mul_pos ht0 (by positivity)
  · exact isOpen_lt (Complex.continuous_re.abs) continuous_const
  · exact isOpen_lt continuous_const Complex.continuous_im
  · rintro z ⟨t, rfl⟩
    change |(verticalPath B t).re| < B / 16
    simpa only [verticalPath_apply, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, abs_zero] using
      (show (0 : ℝ) < B / 16 by positivity)
  · change B / 4 < (((B / 2 : ℝ) : ℂ) * Complex.I).im
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, add_zero] using
      (show B / 4 < B / 2 by linarith)

/-- Ordinary SLE has positive probability of a finite positive first-height
crossing with fresh tip and rectangle-contained past, at each fixed scale. -/
theorem narrowFirstHeight_positive
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (hpublished : PublishedGeometricTubeSupport P γ) {B : ℝ} (hB : 0 < B) :
    0 < P {ω | NarrowFirstHeight B (γ ω)} := by
  obtain ⟨_, _, htrace⟩ := hSLE.2
  have hpos := narrowRiseEvent_positive P γ hpublished hB
  refine hpos.trans_le (measure_mono_ae ?_)
  filter_upwards [htrace] with ω hω
  intro hωrise
  obtain ⟨G, F, hw⟩ := hω
  exact narrowRiseEvent_gives_first_height hB ⟨γ ω, hw.1⟩ hw.2.1 hw.2.2.1 hωrise

end SLEExactGauge.FirstHeightSupport

end

end OAI
