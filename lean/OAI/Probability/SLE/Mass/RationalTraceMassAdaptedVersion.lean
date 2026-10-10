import OAI.Probability.SLE.Mass.RationalTraceMassAdapted
import OAI.Probability.SLE.Mass.SubSigmaRadonLimit

namespace OAI

/-! Rational adapted versions determine one adapted all-time version on the
same probability-one set on which the limiting compact tests are continuous. -/

noncomputable section
open Set Filter MeasureTheory Classical
open scoped Topology NNReal ENNReal CompactlySupported

namespace SLEExactGauge

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

theorem halfPlane_extension_adapted_common_version
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (ℱ : Filtration ℝ≥0 mΩ)
    (μ : ℚ → Ω → Measure upperHalfPlane) (M : ℝ → Ω → Measure upperHalfPlane)
    (hμr : ∀ q ω, (μ q ω).Regular) (hMr : ∀ t ω, (M t ω).Regular)
    (hcont : ∀ᵐ ω ∂P, ∀ f : C_c(upperHalfPlane,ℝ),
      Continuous (fun t => ∫ z, f z ∂M t ω))
    (hrat : ∀ᵐ ω ∂P, ∀ q : ℚ, M q ω = μ q ω)
    (hμm : ∀ q : ℚ, 0 ≤ q → Measurable[ℱ (q : ℝ).toNNReal] (μ q)) :
    ∃ N : ℝ≥0 → Ω → Measure upperHalfPlane, Adapted ℱ N ∧
      (∀ t ω, (N t ω).Regular ∧ IsFiniteMeasureOnCompacts (N t ω)) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, N t ω = M t ω := by
  let Good (ω : Ω) : Prop :=
    (∀ f : C_c(upperHalfPlane,ℝ), Continuous (fun t => ∫ z, f z ∂M t ω)) ∧
      ∀ q : ℚ, M q ω = μ q ω
  have hex (t : ℝ≥0) : ∃ N : Ω → Measure upperHalfPlane,
      Measurable[ℱ t] N ∧ (∀ ω, (N ω).Regular ∧ IsFiniteMeasureOnCompacts (N ω)) ∧
      ∀ ω, Good ω → N ω = M t ω := by
    by_cases ht : t = 0
    · subst t
      refine ⟨μ 0,?_,?_,?_⟩
      · convert hμm (0:ℚ) le_rfl using 1
        norm_num
      · intro ω
        let := hμr 0 ω
        exact ⟨hμr 0 ω,inferInstance⟩
      · intro ω hω
        simpa only [Rat.cast_zero,NNReal.coe_zero] using (hω.2 0).symm
    · have htpos : 0 < (t:ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht)
      obtain ⟨q,_,hq,hqt⟩ := Rat.denseRange_cast.exists_seq_strictMono_tendsto_of_lt
        (fun a b hab => Rat.cast_le.mpr hab) htpos
      have hqm (n : ℕ) : Measurable[ℱ t] (μ (q n)) := by
        have hqn : 0 ≤ q n := Rat.cast_nonneg.mp (hq n).1.le
        have htime : (q n : ℝ).toNNReal ≤ t := by
          simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal (hq n).2.le
        exact (hμm (q n) hqn).mono (ℱ.mono htime) le_rfl
      have hfinite (n : ℕ) (ω : Ω) : IsFiniteMeasureOnCompacts (μ (q n) ω) := by
        let := hμr (q n) ω
        infer_instance
      let : MeasurableSpace Ω := ℱ t
      have hm (n : ℕ) (f : C_c(upperHalfPlane,ℝ)) :
          Measurable[ℱ t] (fun ω => ∫ z, f z ∂μ (q n) ω) :=
        measurable_halfPlane_compact_test_integral (μ (q n)) (hqm n) (hμr (q n)) f
      obtain ⟨N,hNm,hNr,hNe⟩ := exists_subsigma_radon_version_identified
        (ℱ t) (fun n => μ (q n)) hfinite hm
      refine ⟨N,hNm,hNr,?_⟩
      intro ω hω
      apply hNe ω (M t ω) (hMr t ω)
      intro f
      simpa only [Function.comp_def,hω.2] using
        (hω.1 f).continuousAt.tendsto.comp hqt
  choose N hNm hNr hNe using hex
  refine ⟨N,hNm,hNr,?_⟩
  filter_upwards [hcont,hrat] with ω hc hr
  exact fun t => hNe t ω ⟨hc,hr⟩

end SLEExactGauge

end

end OAI
