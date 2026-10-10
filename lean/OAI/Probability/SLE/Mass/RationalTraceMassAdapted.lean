import OAI.Probability.SLE.Mass.RationalTraceMassLocalVariation
import OAI.Probability.SLE.Mass.RadonTestMeasurability

namespace OAI

/-! Adapted and jointly measurable all-time Radon mass, obtained from
rational left limits in the original filtration. -/

noncomputable section
open Set Filter MeasureTheory Classical
open scoped Topology ENNReal NNReal CompactlySupported

namespace SLEExactGauge

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

lemma measurable_halfPlane_compact_test_integral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Ω → Measure upperHalfPlane)
    (hm : Measurable μ) (hr : ∀ ω, (μ ω).Regular) (f : C_c(upperHalfPlane,ℝ)) :
    Measurable (fun ω => ∫ z, f z ∂μ ω) := by
  have hp := (Measure.measurable_lintegral f.continuous.measurable.ennreal_ofReal).comp hm
  have hn := (Measure.measurable_lintegral f.continuous.measurable.neg.ennreal_ofReal).comp hm
  have he (ω : Ω) : (∫ z, f z ∂μ ω) =
      (∫⁻ z, ENNReal.ofReal (f z) ∂μ ω).toReal -
        (∫⁻ z, ENNReal.ofReal (-f z) ∂μ ω).toReal := by
    let := hr ω
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part f.integrable
  simp_rw [he]
  exact hp.ennreal_toReal.sub hn.ennreal_toReal

theorem halfPlane_extension_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 mΩ)
    (μ : ℚ → Ω → Measure upperHalfPlane) (M : ℝ → Ω → Measure upperHalfPlane)
    (hMr : ∀ t ω, (M t ω).Regular)
    (hcont : ∀ ω (f : C_c(upperHalfPlane,ℝ)), Continuous (fun t => ∫ z, f z ∂M t ω))
    (hrat : ∀ (q : ℚ) ω, M q ω = μ q ω)
    (hμm : ∀ q : ℚ, 0 ≤ q → Measurable[ℱ (q : ℝ).toNNReal] (μ q)) :
    Adapted ℱ (fun t : ℝ≥0 => M t) := by
  intro t
  by_cases ht : t = 0
  · subst t
    have he : M (0:ℝ) = μ (0:ℚ) := by
      funext ω
      simpa only [Rat.cast_zero] using hrat 0 ω
    change Measurable[ℱ 0] (M (0:ℝ))
    rw [he]
    convert hμm (0:ℚ) le_rfl using 1
    norm_num
  · have htpos : 0 < (t:ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht)
    obtain ⟨q,_,hq,hqt⟩ := Rat.denseRange_cast.exists_seq_strictMono_tendsto_of_lt
      (fun a b hab => Rat.cast_le.mpr hab) htpos
    let : MeasurableSpace Ω := ℱ t
    apply measurable_radon_of_tests (M t) (hMr t)
    intro f
    have hqm (n : ℕ) : Measurable[ℱ t] (μ (q n)) := by
      have hqn : 0 ≤ q n := Rat.cast_nonneg.mp (hq n).1.le
      have htime : (q n : ℝ).toNNReal ≤ t := by
        simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal (hq n).2.le
      exact (hμm (q n) hqn).mono (ℱ.mono htime) le_rfl
    apply measurable_of_tendsto_metrizable
      (fun n => measurable_halfPlane_compact_test_integral (μ (q n)) (hqm n)
        (fun ω => hrat (q n) ω ▸ hMr (q n) ω) f)
    apply tendsto_pi_nhds.mpr
    intro ω
    simpa only [Function.comp_def,hrat] using
      (hcont ω f).continuousAt.tendsto.comp hqt

/-- Joint measurability follows through real compact-test integrals;
no topology on the space of Radon measures is required. -/
theorem halfPlane_extension_joint_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 mΩ)
    (μ : ℚ → Ω → Measure upperHalfPlane) (M : ℝ → Ω → Measure upperHalfPlane)
    (hMr : ∀ t ω, (M t ω).Regular)
    (hcont : ∀ ω (f : C_c(upperHalfPlane,ℝ)), Continuous (fun t => ∫ z, f z ∂M t ω))
    (hrat : ∀ (q : ℚ) ω, M q ω = μ q ω)
    (hμm : ∀ q : ℚ, 0 ≤ q → Measurable[ℱ (q : ℝ).toNNReal] (μ q)) :
    Measurable (fun q : ℝ≥0 × Ω => M q.1 q.2) := by
  have had := halfPlane_extension_adapted ℱ μ M hMr hcont hrat hμm
  apply measurable_radon_of_tests (fun q : ℝ≥0 × Ω => M q.1 q.2)
    (fun q => hMr q.1 q.2)
  intro f
  apply measurable_uncurry_of_continuous_of_measurable
    (fun ω => (hcont ω f).comp NNReal.continuous_coe)
  intro t
  exact measurable_halfPlane_compact_test_integral (M t) (had.measurable (i := t)) (hMr t) f

theorem halfPlane_extension_progressive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 mΩ)
    (μ : ℚ → Ω → Measure upperHalfPlane) (M : ℝ → Ω → Measure upperHalfPlane)
    (hMr : ∀ t ω, (M t ω).Regular)
    (hcont : ∀ ω (f : C_c(upperHalfPlane,ℝ)), Continuous (fun t => ∫ z, f z ∂M t ω))
    (hrat : ∀ (q : ℚ) ω, M q ω = μ q ω)
    (hμm : ∀ q : ℚ, 0 ≤ q → Measurable[ℱ (q : ℝ).toNNReal] (μ q)) :
    IsProgressive ℱ (fun t : ℝ≥0 => M t) := by
  have had := halfPlane_extension_adapted ℱ μ M hMr hcont hrat hμm
  intro T
  let : MeasurableSpace Ω := ℱ T
  apply measurable_radon_of_tests (fun q : Iic T × Ω => M q.1.1 q.2)
    (fun q => hMr q.1.1 q.2)
  intro f
  apply measurable_uncurry_of_continuous_of_measurable
    (fun ω => (hcont ω f).comp (NNReal.continuous_coe.comp continuous_subtype_val))
  intro t
  have ht : Measurable[ℱ T] (M (t.1 : ℝ)) := had.measurable_le t.2
  exact measurable_halfPlane_compact_test_integral (M (t.1 : ℝ)) ht (hMr t.1) f

end SLEExactGauge

end

end OAI
