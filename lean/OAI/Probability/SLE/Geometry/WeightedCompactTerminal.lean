import OAI.Probability.SLE.Mass.WeightedCompactMass
import OAI.Probability.SLE.Mass.MassCompensatorRecovery

namespace OAI

/-! The compact weighted canonical mass is a continuous increasing scalar
process with an integrable squared terminal bound. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint

def compactWeightedMass (w : C(upperHalfPlane,ℝ≥0))
    (K : Set upperHalfPlane) (μ : Measure upperHalfPlane) : ℝ :=
  ∫ z in K, (w z:ℝ) ∂μ

lemma compactWeightedMass_eq_lintegral (w : C(upperHalfPlane,ℝ≥0))
    (K : Set upperHalfPlane) (μ : Measure upperHalfPlane) :
    compactWeightedMass w K μ = (∫⁻ z in K, (w z:ℝ≥0∞) ∂μ).toReal := by
  have h := integral_eq_lintegral_of_nonneg_ae
    (μ := μ.restrict K) (ae_of_all _ (fun z => (w z).coe_nonneg))
    (continuous_subtype_val.comp w.continuous).measurable.aestronglyMeasurable
  simpa only [compactWeightedMass,ENNReal.ofReal_coe_nnreal] using h

lemma compactWeightedMass_measurable (w : C(upperHalfPlane,ℝ≥0))
    (K : Set upperHalfPlane) (hK : MeasurableSet K) :
    Measurable (compactWeightedMass w K) := by
  have he : compactWeightedMass w K =
      (fun μ => (∫⁻ z, K.indicator (fun z => (w z:ℝ≥0∞)) z ∂μ).toReal) := by
    funext μ
    rw [compactWeightedMass_eq_lintegral,lintegral_indicator hK]
  rw [he]
  exact (Measure.measurable_lintegral
    (w.continuous.measurable.coe_nnreal_ennreal.indicator hK)).ennreal_toReal

lemma compactWeightedMass_nonneg (w : C(upperHalfPlane,ℝ≥0))
    (K : Set upperHalfPlane) (μ : Measure upperHalfPlane) :
    0 ≤ compactWeightedMass w K μ :=
  integral_nonneg (fun z => (w z).coe_nonneg)

@[simp] lemma compactWeightedMass_zero (w : C(upperHalfPlane,ℝ≥0))
    (K : Set upperHalfPlane) : compactWeightedMass w K 0 = 0 := by
  simp [compactWeightedMass]

lemma compactWeightedMass_mono (w : C(upperHalfPlane,ℝ≥0))
    (K : Set upperHalfPlane) (hK : IsCompact K)
    {μ ν : Measure upperHalfPlane} [IsFiniteMeasureOnCompacts ν] (hμν : μ ≤ ν) :
    compactWeightedMass w K μ ≤ compactWeightedMass w K ν := by
  let : IsFiniteMeasure (μ.restrict K) :=
    ⟨lt_of_le_of_lt (Measure.restrict_mono le_rfl hμν univ) (by simpa using hK.measure_lt_top (μ := ν))⟩
  let : IsFiniteMeasure (ν.restrict K) := ⟨by simpa using hK.measure_lt_top (μ := ν)⟩
  obtain ⟨M,hM⟩ := compact_weight_bounded w K hK
  exact sub_nonneg.mp (integral_weight_difference_le (μ.restrict K) (ν.restrict K)
    (Measure.restrict_mono le_rfl hμν) _ (compact_weight_integrable w K hK ν) M
    (ae_of_all _ (fun z => (w z).coe_nonneg))
    ((ae_restrict_mem hK.measurableSet).mono (fun z hz => NNReal.coe_le_coe.mpr (hM z hz)))).1

lemma compactWeightedMass_le (w : C(upperHalfPlane,ℝ≥0))
    (K : Set upperHalfPlane) (hK : IsCompact K)
    (M : ℝ≥0) (hM : ∀ z ∈ K, w z ≤ M)
    (μ : Measure upperHalfPlane) [IsFiniteMeasureOnCompacts μ] :
    compactWeightedMass w K μ ≤ (M:ℝ)*(μ K).toReal := by
  let : IsFiniteMeasure (μ.restrict K) := ⟨by simpa using hK.measure_lt_top (μ := μ)⟩
  have h := integral_mono_ae (compact_weight_integrable w K hK μ)
    (integrable_const (μ := μ.restrict K) (M:ℝ))
    ((ae_restrict_mem hK.measurableSet).mono (fun z hz => NNReal.coe_le_coe.mpr (hM z hz)))
  simpa only [compactWeightedMass,integral_const,smul_eq_mul,measureReal_def,
    Measure.restrict_apply_univ,mul_comm] using h

lemma compactWeightedMass_tendsto
    (w : C(upperHalfPlane,ℝ≥0)) (K : Set upperHalfPlane) (hK : IsCompact K)
    (N : ℝ≥0 → Measure upperHalfPlane) (ν : Measure upperHalfPlane)
    [IsFiniteMeasureOnCompacts ν] (hNr : ∀ t, IsFiniteMeasureOnCompacts (N t))
    (hdom : ∀ t, N t ≤ ν)
    (hlim : Tendsto (fun t => (ν-N t) K) atTop (𝓝 0)) :
    Tendsto (fun t => compactWeightedMass w K (N t)) atTop
      (𝓝 (compactWeightedMass w K ν)) := by
  obtain ⟨M,hM⟩ := compact_weight_bounded w K hK
  have hb (t : ℝ≥0) : |compactWeightedMass w K (N t)-compactWeightedMass w K ν| ≤
      (M:ℝ)*((ν-N t) K).toReal := by
    let := hNr t
    have h := compact_weight_difference_le w K hK M hM (N t) ν (hdom t)
    have he : ((ν-N t) K).toReal = (ν K).toReal-(N t K).toReal := by
      rw [sub_apply_of_finite_restriction (hdom t) hK.measurableSet hK.measure_lt_top.ne,
        ENNReal.toReal_sub_of_le (hdom t K) hK.measure_lt_top.ne]
    rw [he]
    have hn : (N t K).toReal ≤ (ν K).toReal :=
      ENNReal.toReal_mono hK.measure_lt_top.ne (hdom t K)
    simpa only [compactWeightedMass,abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hn)] using h
  have hl : Tendsto (fun t => (M:ℝ)*((ν-N t) K).toReal) atTop (𝓝 0) := by
    simpa only [Function.comp_def,ENNReal.toReal_zero,mul_zero] using
      tendsto_const_nhds.mul ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim)
  have hz := squeeze_zero (fun t => abs_nonneg (compactWeightedMass w K (N t)-
    compactWeightedMass w K ν)) hb hl
  exact tendsto_iff_dist_tendsto_zero.mpr (by simpa only [Real.dist_eq] using hz)

namespace CanonicalMass

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

lemma compactWeightedMass_terminal_memLp
    (w : C(upperHalfPlane,ℝ≥0)) (K : Set upperHalfPlane) (hK : IsCompact K) :
    MemLp (fun ω => compactWeightedMass w K (C.rational.terminal ω)) 2 P := by
  obtain ⟨M,hM⟩ := compact_weight_bounded w K hK
  have hm := (Measure.measurable_coe hK.measurableSet).comp C.rational.terminal_measurable
  have hLp := memLp_toReal_two P _ hm _ (C.rational.moments K hK 2) le_rfl
  apply (hLp.const_mul (M:ℝ)).mono'
    ((compactWeightedMass_measurable w K hK.measurableSet).comp
      C.rational.terminal_measurable).aestronglyMeasurable
  filter_upwards [] with ω
  let := (C.rational.terminal_radon ω).2
  dsimp only [Function.comp_def]
  rw [Real.norm_of_nonneg (compactWeightedMass_nonneg w K _)]
  exact compactWeightedMass_le w K hK M hM _

lemma compactWeightedMass_paths
    (w : C(upperHalfPlane,ℝ≥0)) (K : Set upperHalfPlane) (hK : IsCompact K) :
    ∀ᵐ ω ∂P, Monotone (fun t => compactWeightedMass w K (C.process t ω)) ∧
      compactWeightedMass w K (C.process 0 ω)=0 ∧
      Continuous (fun t => compactWeightedMass w K (C.process t ω)) ∧
      Tendsto (fun t => compactWeightedMass w K (C.process t ω)) atTop
        (𝓝 (compactWeightedMass w K (C.rational.terminal ω))) ∧
      ∀ t, compactWeightedMass w K (C.process t ω) ≤
        compactWeightedMass w K (C.rational.terminal ω) := by
  filter_upwards [C.paths,C.exhaustion] with ω hp he
  let := (C.rational.terminal_radon ω).2
  refine ⟨?_,?_,hp.weighted_compact_continuous (fun t => (C.radon t ω).2) w K hK,
    compactWeightedMass_tendsto w K hK _ _ (fun t => (C.radon t ω).2) hp.dominated (he K hK),?_⟩
  · intro s t hst
    let := (C.radon t ω).2
    exact compactWeightedMass_mono w K hK (hp.monotone hst)
  · rw [hp.zero,compactWeightedMass_zero]
  · intro t
    exact compactWeightedMass_mono w K hK (hp.dominated t)

end CanonicalMass
end SLEExactGauge.Multipoint

end

end OAI
