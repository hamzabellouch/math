import OAI.Analysis.PlanarEndpoint.Fourier
import OAI.Analysis.PlanarEndpoint.FrequencyWeak
import OAI.Analysis.PlanarEndpoint.GraphDual
import OAI.Analysis.PlanarEndpoint.WeakIntegration

namespace OAI

/-! Gaussian regularization, Fourier evolution and endpoint maximal estimates. -/


noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
namespace PlanarEndpoint

lemma integrable_of_memLp_annular {v : Plane → ℂ} (hv : MemLp v 2 volume)
    {c₀ C₀ N : ℝ}
    (hs : ∀ᵐ ξ : Plane ∂volume, ξ ∉ {ξ | c₀*N ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ C₀*N} → v ξ = 0) :
    Integrable v volume := by
  have hi := ((hv.locallyIntegrable (by norm_num)).integrableOn_isCompact
    (isCompact_closedBall (0 : Plane) (C₀*N))).integrable_indicator measurableSet_closedBall
  apply hi.congr
  filter_upwards [hs] with ξ hξ
  by_cases h : ξ ∈ Metric.closedBall (0 : Plane) (C₀*N)
  · rw [indicator_of_mem h]
  · rw [indicator_of_notMem h]
    symm
    apply hξ
    intro hh
    exact h (by simpa using hh.2)

lemma frequency_graph_integral_bound {c₀ C₀ p : ℝ} (hp : 1 < p)
    {C : ℝ} (hC : 0 ≤ C) {j : ℕ} {v : Plane → ℂ} (hv : MemLp v 2 volume)
    (hs : ∀ᵐ ξ : Plane ∂volume, ξ ∉ {ξ | c₀*(2:ℝ)^j ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ C₀*(2:ℝ)^j} → v ξ = 0)
    {x₀ : Plane} {t₀ s : ℝ}
    (hweak : ∀ lam : ℝ, 0 < lam →
      volume (Metric.ball x₀ 1 ∩ {x | ∃ t ∈ Icc t₀ (t₀+s), lam < ‖frequencyExtension v x t‖}) ≤
        ENNReal.ofReal ((C*((2:ℝ)^j)^(1/3:ℝ)*‖hv.toLp v‖/lam)^p))
    {E : Set Plane} (hE : MeasurableSet E) (hEB : E ⊆ Metric.ball x₀ 1)
    {T : Plane → ℝ} (hT : Measurable T) (hTs : ∀ x ∈ E, T x ∈ Icc t₀ (t₀+s)) :
    IntegrableOn (fun x => frequencyExtension v x (T x)) E volume ∧
    (∫ x in E, ‖frequencyExtension v x (T x)‖) ≤
      p/(p-1)*C*((2:ℝ)^j)^(1/3:ℝ)*‖hv.toLp v‖*(volume.real E)^(1-1/p) := by
  have hfin : volume E ≠ ⊤ := (measure_mono hEB |>.trans_lt measure_ball_lt_top).ne
  let : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.2 hfin
  have hi := integrable_of_memLp_annular hv hs
  have hm : Measurable (fun x => frequencyExtension v x (T x)) :=
    by simpa only [Function.comp_def, id_eq] using
      (continuous_frequencyExtension hi).measurable.comp (measurable_id.prodMk hT)
  have hw : ∀ lam : ℝ, 0 < lam →
      (volume.restrict E) {x | lam < ‖frequencyExtension v x (T x)‖} ≤
        ENNReal.ofReal ((C*((2:ℝ)^j)^(1/3:ℝ)*‖hv.toLp v‖/lam)^p) := by
    intro lam hlam
    rw [Measure.restrict_apply' hE]
    apply le_trans (measure_mono ?_) (hweak lam hlam)
    rintro x ⟨hx,hxE⟩
    exact ⟨hEB hxE, T x, hTs x hxE, hx⟩
  have hh := weak_integral_norm_bound (volume.restrict E) hm.aestronglyMeasurable hp
    (show 0 ≤ C*((2:ℝ)^j)^(1/3:ℝ)*‖hv.toLp v‖ by positivity) hw
  simpa only [IntegrableOn, Measure.restrict_apply_univ, measureReal_def, mul_assoc] using hh

lemma graphFourier_frequency_pairing {v : Plane → ℂ} (hv : Integrable v volume)
    (μ : Measure Plane) [IsFiniteMeasure μ] {T : Plane → ℝ} {w : Plane → ℂ}
    (hT : Measurable T) (hw : Measurable w) (hb : ∀ x, ‖w x‖ ≤ 1) :
    (∫ ξ, v ξ * graphFourier μ T w ξ) = ∫ x, w x * frequencyExtension v x (T x) ∂μ := by
  have hi : Integrable (fun z : Plane × Plane => v z.1 * (w z.2 * phase z.2 (T z.2) z.1))
      (volume.prod μ) := by
    apply (hv.norm.comp_fst μ).mono'
    · exact ((hv.aestronglyMeasurable.comp_fst).mul
        ((hw.comp measurable_snd).aestronglyMeasurable.mul
          ((measurable_graph_phase hT).comp measurable_swap).aestronglyMeasurable))
    · filter_upwards [] with z
      simp only [norm_mul, norm_phase, mul_one]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hb z.2) (norm_nonneg (v z.1))
  calc
    _ = ∫ ξ, ∫ x, v ξ * (w x * phase x (T x) ξ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [integral_const_mul]
      rfl
    _ = ∫ x, (∫ ξ, v ξ * (w x * phase x (T x) ξ)) ∂μ := integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      unfold frequencyExtension
      rw [← integral_const_mul]
      congr 1
      funext ξ
      ring

lemma norm_toLp_le_const_mul {v g : Plane → ℂ} (hv : MemLp v 2 volume)
    (hg : MemLp g 2 volume) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᵐ ξ ∂volume, ‖v ξ‖ ≤ B * ‖g ξ‖) :
    ‖hv.toLp v‖ ≤ B * ‖hg.toLp g‖ := by
  have hi : ∫ ξ, ‖v ξ‖^2 ≤ B^2 * ∫ ξ, ‖g ξ‖^2 := by
    rw [← integral_const_mul]
    apply integral_mono_ae ((memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).1 hv)
      (((memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg).const_mul _)
    filter_upwards [hb] with ξ hξ
    nlinarith [norm_nonneg (v ξ), norm_nonneg (g ξ)]
  have he {a : Plane → ℂ} (ha : MemLp a 2 volume) : (∫ ξ, ‖a ξ‖^2) = ‖ha.toLp a‖^2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp] with ξ hξ
    simp only [hξ, real_inner_self_eq_norm_sq]
  rw [he hv, he hg] at hi
  have hn : 0 ≤ B * ‖hg.toLp g‖ := by positivity
  nlinarith [norm_nonneg (hv.toLp v)]

lemma memLp_mul_conj_bounded {χ g : Plane → ℂ} (hχ : Measurable χ)
    (hg : MemLp g 2 volume) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ ξ, ‖χ ξ‖ ≤ B) :
    MemLp (fun ξ => χ ξ * conj (g ξ)) 2 volume := by
  apply (hg.const_mul (B : ℂ)).mono
  · exact hχ.aestronglyMeasurable.mul hg.aestronglyMeasurable.star
  · filter_upwards [] with ξ
    simp only [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hB]
    exact mul_le_mul_of_nonneg_right (hb ξ) (norm_nonneg (g ξ))

lemma graphLp_dual_test_identity (χ : Plane → ℂ) (hχ : MemLp χ 2 volume)
    (μ : Measure Plane) [IsFiniteMeasure μ] (T : Plane → ℝ) (w : Plane → ℂ)
    (hT : Measurable T) (hw : Measurable w) (hb : ∀ x, ‖w x‖ ≤ 1)
    (hv : Integrable (fun ξ => χ ξ * conj (graphDual χ μ T w ξ)) volume) :
    ‖graphLp χ hχ μ T w hT hw hb‖^2 =
      ‖∫ x, w x * frequencyExtension (fun ξ => χ ξ * conj (graphDual χ μ T w ξ)) x (T x) ∂μ‖ := by
  rw [← graphFourier_frequency_pairing hv μ hT hw hb]
  calc
    _ = ‖inner ℂ (graphLp χ hχ μ T w hT hw hb) (graphLp χ hχ μ T w hT hw hb)‖ := by
      rw [← inner_self_re_eq_norm, norm_sq_eq_re_inner (𝕜 := ℂ)]
    _ = ‖∫ ξ, graphDual χ μ T w ξ * conj (graphDual χ μ T w ξ)‖ :=
      congrArg norm (inner_graphLp χ hχ μ μ T w hT hw hb)
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with ξ
      unfold graphDual
      ring

lemma graph_mass_bound_of_shortTime {c₀ C₀ p : ℝ} (hp : 1 < p)
    (hshort : ShortTimeWeakEstimate c₀ C₀ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, ∀ (χ : Plane → ℂ) (_ : Measurable χ)
      (hχ : MemLp χ 2 volume) (B : ℝ), 0 ≤ B → (∀ ξ, ‖χ ξ‖ ≤ B) →
      (∀ᵐ ξ : Plane ∂volume,
        ξ ∉ {ξ | c₀*(2:ℝ)^j ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ C₀*(2:ℝ)^j} → χ ξ = 0) →
      ∀ (x₀ : Plane) (t₀ s : ℝ), 0 ≤ s → s ≤ ((2:ℝ)^j)⁻¹ →
      ∀ (E : Set Plane), MeasurableSet E → E ⊆ Metric.ball x₀ 1 →
      ∀ (T : Plane → ℝ) (w : Plane → ℂ) (hT : Measurable T) (hw : Measurable w)
      (hb : ∀ x, ‖w x‖ ≤ 1), (∀ x ∈ E, T x ∈ Icc t₀ (t₀+s)) →
      ∀ [IsFiniteMeasure (volume.restrict E)],
      ‖graphLp χ hχ (volume.restrict E) T w hT hw hb‖ ≤
        C * B * ((2:ℝ)^j)^(1/3:ℝ) * (volume.real E)^(1-1/p) := by
  obtain ⟨C,hC,hwk⟩ := frequency_weak_of_shortTime hshort
  refine ⟨p/(p-1)*C, mul_pos (div_pos (by linarith) (by linarith)) hC, ?_⟩
  intro j χ hχm hχ B hB hχB hχs x₀ t₀ s hs hs' E hE hEB T w hT hw hb hTs inst
  let μ := volume.restrict E
  let g := graphDual χ μ T w
  have hg : MemLp g 2 volume := graphDual_memLp χ hχ μ hT hw hb
  let v : Plane → ℂ := fun ξ => χ ξ * conj (g ξ)
  have hv : MemLp v 2 volume := memLp_mul_conj_bounded hχm hg hB hχB
  have hvs : ∀ᵐ ξ : Plane ∂volume,
      ξ ∉ {ξ | c₀*(2:ℝ)^j ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ C₀*(2:ℝ)^j} → v ξ = 0 := by
    filter_upwards [hχs] with ξ hξ hh
    simp only [v, hξ hh, zero_mul]
  have hn : ‖hv.toLp v‖ ≤ B * ‖hg.toLp g‖ := by
    apply norm_toLp_le_const_mul hv hg hB
    filter_upwards [] with ξ
    simp only [v, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right (hχB ξ) (norm_nonneg (g ξ))
  have hh := frequency_graph_integral_bound hp hC.le hv hvs
    (fun lam hlam => hwk j v hv hvs x₀ t₀ s lam hs hs' hlam) hE hEB hT hTs
  have hpair := graphLp_dual_test_identity χ hχ μ T w hT hw hb
    (integrable_of_memLp_annular hv hvs)
  have hhi : Integrable (fun x => frequencyExtension v x (T x)) μ := hh.1
  have hi : Integrable (fun x => w x * frequencyExtension v x (T x)) μ := by
    apply hhi.norm.mono'
    · exact hw.aestronglyMeasurable.mul hhi.aestronglyMeasurable
    · filter_upwards [] with x
      simpa only [norm_mul, one_mul] using
        mul_le_mul_of_nonneg_right (hb x) (norm_nonneg (frequencyExtension v x (T x)))
  have hh' : ‖graphLp χ hχ μ T w hT hw hb‖^2 ≤
      p/(p-1)*C*((2:ℝ)^j)^(1/3:ℝ)*‖hv.toLp v‖*(volume.real E)^(1-1/p) := by
    rw [hpair]
    apply (norm_integral_le_integral_norm _).trans
    apply le_trans (integral_mono hi.norm hhi.norm ?_) hh.2
    intro x
    simpa only [norm_mul, one_mul] using
      mul_le_mul_of_nonneg_right (hb x) (norm_nonneg (frequencyExtension v x (T x)))
  change ‖hg.toLp g‖ ≤ _
  change ‖hg.toLp g‖^2 ≤ _ at hh'
  have hfac : 0 ≤ p/(p-1)*C*((2:ℝ)^j)^(1/3:ℝ) * (volume.real E)^(1-1/p) := by
    have : 0 ≤ p/(p-1) := div_nonneg (by linarith) (by linarith)
    positivity
  have hmul := mul_le_mul_of_nonneg_left hn hfac
  have hzero := norm_nonneg (hg.toLp g)
  by_cases hz : ‖hg.toLp g‖ = 0
  · rw [hz]
    have := mul_nonneg hfac hB
    nlinarith
  · have hpos : 0 < ‖hg.toLp g‖ := lt_of_le_of_ne hzero (Ne.symm hz)
    nlinarith

end PlanarEndpoint
end

end OAI
