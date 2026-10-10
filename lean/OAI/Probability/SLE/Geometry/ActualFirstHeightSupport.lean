import OAI.Probability.SLE.Stochastic.BrownianFiniteSmallBall
import OAI.Probability.SLE.Loewner.SmallDriverRise
import OAI.Probability.SLE.Geometry.FirstHeightSupport

namespace OAI

/-! The narrow first-height support event is proved directly from the
Brownian driver and the deterministic Loewner equation. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open FirstHeightSupport

theorem regular_strip_rise_positive
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) {A H : ℝ} (hA : 0 < A) (hH : 0 ≤ H) :
    0 < (P.comap (Subtype.val : a.samples → Ω))
      {ω | ∃ T : ℝ≥0, 0 < T ∧ MapsTo (γ ω) (Icc 0 T) {z : ℂ | |z.re| < A} ∧
        H < (γ ω T).im} := by
  let T : ℝ≥0 := ⟨(H+1)^2,sq_nonneg _⟩
  have hT : 0 < T := by change 0 < (H+1)^2; positivity
  have hHT : H < 2*Real.sqrt T := by
    change H < 2*Real.sqrt ((H+1)^2)
    rw [Real.sqrt_sq (by linarith : 0 ≤ H+1)]
    linarith
  obtain ⟨δ,hδ,hrise⟩ := exists_small_driver_rise T H hH hHT
  let ε := min δ (A/2)
  have hε : 0 < ε := lt_min hδ (by positivity)
  have hroot : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hp := brownian_finite_smallBall_positive a.B a.brownian a.measurable_B
    a.continuous_B a.zero_B T hT (div_pos hε hroot)
  apply hp.trans_le (measure_mono ?_)
  intro ω hω
  have hu (t : ℝ≥0) (ht : t ∈ Icc 0 T) : |Real.sqrt κ*a.B t ω| < ε := by
    rw [abs_mul,abs_of_pos hroot]
    have hh := (lt_div_iff₀ hroot).mp (hω t ht)
    nlinarith
  obtain ⟨τ,hτ,hhigh⟩ := hrise (fun t => Real.sqrt κ*a.B t ω) (γ ω)
    (a.G ω) (a.F ω) (a.witness ω) (fun t ht => (hu t ht).le.trans (min_le_left _ _))
  have hτ0 : 0 < τ := by
    by_contra hn
    have he : τ=0 := le_antisymm (le_of_not_gt hn) zero_le
    rw [he,(a.witness ω).2.1,Complex.zero_im] at hhigh
    linarith
  refine ⟨τ,hτ0,?_,hhigh⟩
  intro t ht
  have hb := (a.witness ω).trace_abs_re_le t (M := ε)
    (fun s hs => (hu s ⟨zero_le,hs.2.trans (ht.2.trans hτ.2)⟩).le)
  change |(γ ω t).re| < A
  exact hb.trans_lt (lt_of_le_of_lt (min_le_right _ _) (by linarith))


theorem regular_narrowRise_positive
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) {B : ℝ} (hB : 0 < B) :
    0 < (P.comap (Subtype.val : a.samples → Ω))
      {ω | ∃ T : ℝ≥0, 0 < T ∧ MapsTo (γ ω) (Icc 0 T) (narrowStrip B) ∧
        γ ω T ∈ aboveQuarterHeight B} :=
  regular_strip_rise_positive a hκ (by positivity : 0 < B/16) (by positivity : 0 ≤ B/4)

theorem ordinary_strip_rise_positive
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (γ : Ω → ℝ≥0 → ℂ)
    (hSLE : IsOrdinaryChordalSLE κ γ P) {A H : ℝ} (hA : 0 < A) (hH : 0 ≤ H) :
    0 < P {ω | ∃ T : ℝ≥0, 0 < T ∧ MapsTo (γ ω) (Icc 0 T) {z : ℂ | |z.re| < A} ∧
      H < (γ ω T).im} := by
  obtain ⟨a⟩ := exists_regular_sle_presentation hSLE
  have hp := regular_strip_rise_positive a hκ hA hH
  apply hp.trans_le
  have hh := Measure.le_map_apply (μ := P.comap (Subtype.val : a.samples → Ω))
    a.measurePreserving_val.measurable.aemeasurable
    {ω | ∃ T : ℝ≥0, 0 < T ∧ MapsTo (γ ω) (Icc 0 T) {z : ℂ | |z.re| < A} ∧
      H < (γ ω T).im}
  rw [a.measurePreserving_val.map_eq] at hh
  convert! hh using 1

theorem ordinary_narrowRise_positive
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (γ : Ω → ℝ≥0 → ℂ)
    (hSLE : IsOrdinaryChordalSLE κ γ P) {B : ℝ} (hB : 0 < B) :
    0 < P {ω | ∃ T : ℝ≥0, 0 < T ∧ MapsTo (γ ω) (Icc 0 T) (narrowStrip B) ∧
      γ ω T ∈ aboveQuarterHeight B} := by
  obtain ⟨a⟩ := exists_regular_sle_presentation hSLE
  have hp := regular_narrowRise_positive a hκ hB
  apply hp.trans_le
  have hh := Measure.le_map_apply (μ := P.comap (Subtype.val : a.samples → Ω))
    a.measurePreserving_val.measurable.aemeasurable
    {ω | ∃ T : ℝ≥0, 0 < T ∧ MapsTo (γ ω) (Icc 0 T) (narrowStrip B) ∧
      γ ω T ∈ aboveQuarterHeight B}
  rw [a.measurePreserving_val.map_eq] at hh
  convert! hh using 1

theorem ordinary_narrowFirstHeight_positive
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (γ : Ω → ℝ≥0 → ℂ)
    (hSLE : IsOrdinaryChordalSLE κ γ P) {B : ℝ} (hB : 0 < B) :
    0 < P {ω | NarrowFirstHeight B (γ ω)} := by
  obtain ⟨_,_,htrace⟩ := hSLE.2
  apply (ordinary_narrowRise_positive P κ hκ γ hSLE hB).trans_le
  apply measure_mono_ae
  filter_upwards [htrace] with ω hω
  intro hrise
  obtain ⟨G,F,hw⟩ := hω
  exact narrowRiseEvent_gives_first_height hB ⟨γ ω,hw.1⟩ hw.2.1 hw.2.2.1 hrise

end SLEExactGauge

end

end OAI
