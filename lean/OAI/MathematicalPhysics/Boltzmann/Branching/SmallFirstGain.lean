import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveVolterra
import OAI.MathematicalPhysics.Boltzmann.Branching.AxisInput
import OAI.MathematicalPhysics.Boltzmann.Branching.SlopedChart
import OAI.MathematicalPhysics.Boltzmann.Branching.WidthTails

namespace OAI

section

/-! # A uniform small-input bound for small transverse incoming velocities -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.SlopedChart
open BoltzmannNonuniqueness.AffineSlices

namespace BoltzmannNonuniqueness.SmallInputGeometry

def fiber (q : ℝ) (v p : Velocity) (R δ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖normal v p‖⁻¹) * ∫⁻ z : ℝ, ∫⁻ s : ℝ,
    if ‖chart v p z s - v‖ ≤ R ∧ ‖transverse (chart v p z s)‖ < δ then
      weightRatio q v (chart v p z s) else 0

theorem abs_axial_le_norm (v : Velocity) : |axial v| ≤ ‖v‖ := by
  have h := norm_sq_split v
  nlinarith [sq_abs (axial v), sq_nonneg ‖transverse v‖, abs_nonneg (axial v), norm_nonneg v]

theorem fiber_le_smallFiber (q : ℝ) (v p : Velocity) (R δ : ℝ) :
    fiber q v p R δ ≤ smallFiber q v p δ := by
  unfold fiber smallFiber
  apply mul_le_mul' le_rfl
  apply lintegral_mono
  intro z
  apply lintegral_mono
  intro s
  dsimp only
  by_cases h : ‖chart v p z s - v‖ ≤ R ∧ ‖transverse (chart v p z s)‖ < δ
  · rw [ite_eq_left h, ite_eq_left h.2]
  · rw [ite_eq_right h]
    exact bot_le

def threshold (r R : ℝ) : ℝ := r ^ 2 / (8 * R)

theorem threshold_pos {r R : ℝ} (hr : 0 < r) (hR : 0 < R) : 0 < threshold r R := by
  unfold threshold
  positivity

theorem fiber_eq_zero_of_small_mismatch {r R δ : ℝ}
    (hr : 0 < r) (hR : 0 < R) (hδ : δ < r / 3) (q : ℝ) (v p : Velocity)
    (hv : r ≤ ‖transverse v‖) (hp : ‖transverse p‖ ≤ r / 4)
    (ha : |axial (v - p)| ≤ threshold r R) : fiber q v p R δ = 0 := by
  have he (z s : ℝ) : ¬(‖chart v p z s - v‖ ≤ R ∧ ‖transverse (chart v p z s)‖ < δ) := by
    intro h
    have hz : |z| ≤ R := by
      have hb := (abs_axial_le_norm (chart v p z s - v)).trans h.1
      simpa only [axial_sub, axial_chart, add_sub_cancel_left] using hb
    have haway := AxisGeometry.chart_exclusion hr hR hv hp ha (s := s) hz
    linarith [h.2]
  unfold fiber
  simp only [ite_eq_right (he _ _), lintegral_zero, mul_zero]

theorem fiber_uniform_bound {q r R δ : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hr : 0 < r) (hR : 0 < R)
    (hδ₀ : 0 ≤ δ) (hδ : δ < r / 3) (v p : Velocity)
    (hv : r ≤ ‖transverse v‖) (hp : ‖transverse p‖ ≤ r / 4) :
    fiber q v p R δ ≤ ENNReal.ofReal (rectangleConstant q δ δ / threshold r R) := by
  have ht := threshold_pos hr hR
  by_cases ha : |axial (v - p)| ≤ threshold r R
  · rw [fiber_eq_zero_of_small_mismatch hr hR hδ q v p hv hp ha]
    exact bot_le
  · have ha' : threshold r R < |axial (v - p)| := lt_of_not_ge ha
    have hane : axial (v - p) ≠ 0 := by intro hz; rw [hz, abs_zero] at ha'; linarith
    have hn : normal v p ≠ 0 := by
      have h := AxisGeometry.normal_lower_bound hv hp
      rw [normal, transverse_sub]
      exact norm_pos_iff.mp (lt_of_lt_of_le (by positivity) h)
    apply (fiber_le_smallFiber q v p R δ).trans
    apply (smallFiber_slope_bound hq₁ hq₂ hδ₀ v p hn hane).trans
    apply ENNReal.ofReal_le_ofReal
    have hK := rectangleConstant_nonneg hq₁ hq₂ hδ₀ hδ₀
    have hW : 1 ≤ W q v := by
      unfold W
      exact le_add_of_nonneg_right (singularity_nonneg q (transverse v))
    have hd : threshold r R ≤ W q v * |axial (v - p)| := by
      nlinarith [abs_nonneg (axial (v - p))]
    exact div_le_div_of_nonneg_left hK ht hd

end BoltzmannNonuniqueness.SmallInputGeometry

end

end

section

/-! # Uniform small-input estimates off the axis -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.UniformGain

namespace BoltzmannNonuniqueness.SmallInput

def region (v : Velocity) (R δ : ℝ) : Set Coordinates :=
  ballRegion v R ∩ {y | ‖transverse (chart v y.1 y.2.1 y.2.2)‖ < δ}

def lowIncoming (r : ℝ) : Set Velocity := {p | ‖transverse p‖ ≤ r / 4}

def lowRegion (v : Velocity) (r R δ : ℝ) : Set Coordinates :=
  region v R δ ∩ (lowIncoming r ×ˢ univ)

theorem measurableSet_region (v : Velocity) (R δ : ℝ) : MeasurableSet (region v R δ) :=
  (measurableSet_ballRegion v R).inter (measurableSet_lt
    (measurable_transverse.comp (measurable_point v)).norm measurable_const)

theorem measurableSet_lowIncoming (r : ℝ) : MeasurableSet (lowIncoming r) :=
  measurableSet_le measurable_transverse.norm measurable_const

theorem measurableSet_lowRegion (v : Velocity) (r R δ : ℝ) : MeasurableSet (lowRegion v r R δ) :=
  (measurableSet_region v R δ).inter ((measurableSet_lowIncoming r).prod .univ)

theorem weight_lowRegion_bound {q r R δ : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hr : 0 < r) (hR : 0 < R) (hδ₀ : 0 ≤ δ) (hδ : δ < r / 3)
    (c : Measure Velocity) [IsProbabilityMeasure c] {v : Velocity} (hv : r ≤ ‖transverse v‖) :
    ChartKernel.measure c (weightRatio q v) v (lowRegion v r R δ) ≤
      2 * ENNReal.ofReal (AffineSlices.rectangleConstant q δ δ / SmallInputGeometry.threshold r R) := by
  have he : ChartKernel.measure c (weightRatio q v) v (lowRegion v r R δ) =
      ChartKernel.measure (c.restrict (lowIncoming r)) (weightRatio q v) v (region v R δ) := by
    rw [measure_restrict_incoming c _ _ (measurableSet_lowIncoming r),
      Measure.restrict_apply (measurableSet_region v R δ)]
    rfl
  rw [he, ← region_eq_measure _ (measurable_weightRatio q v) v (measurableSet_region v R δ)]
  simp only [chartRegionGain, region, Set.indicator, mem_inter_iff, mem_ofPred_eq,
    ballRegion]
  change 2 * (∫⁻ p, SmallInputGeometry.fiber q v p R δ ∂c.restrict (lowIncoming r)) ≤ _
  apply mul_le_mul' le_rfl
  have hbound : (∫⁻ p, SmallInputGeometry.fiber q v p R δ ∂c.restrict (lowIncoming r)) ≤
      ∫⁻ _p in lowIncoming r, ENNReal.ofReal
        (AffineSlices.rectangleConstant q δ δ / SmallInputGeometry.threshold r R) ∂c := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (measurableSet_lowIncoming r)] with p hp
    exact SmallInputGeometry.fiber_uniform_bound hq₁ hq₂ hr hR hδ₀ hδ v p hv hp
  apply hbound.trans
  rw [lintegral_const, Measure.restrict_apply_univ]
  exact mul_le_of_le_one_right zero_le prob_le_one

theorem normalized_lowRegion_bound {q d r R δ L : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8)
    (hr : 0 < r) (hR : 0 < R) (hδ₀ : 0 ≤ δ) (hδ : δ < r / 3)
    {v : Velocity} (hv : r ≤ ‖transverse v‖)
    {ρ : Measure ℝ} [IsProbabilityMeasure ρ] (hρ : AxialMoment ρ L) :
    normalizedMeasure (sheetLaw d ρ) q v (lowRegion v r R δ) ≤
      ENNReal.ofReal tiltConstant * (ENNReal.ofReal (4 * L) *
        (2 * ENNReal.ofReal (AffineSlices.rectangleConstant q δ δ /
          SmallInputGeometry.threshold r R))) := by
  have hnorm := normalized_restriction_le (sheetLaw d ρ) q v
    (measurableSet_lowRegion v r R δ) (measurableSet_lowRegion v r R δ) (Subset.refl _)
    (B := 1) (by norm_num)
    (fun _ _ => Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _)))
  simp only [mul_one] at hnorm
  have hdom := measure_mono_incoming (tiltedSheet_le_probability hd hdmax hρ)
    (weightRatio q v) v (lowRegion v r R δ)
  rw [measure_smul, Measure.smul_apply, smul_eq_mul] at hdom
  have := sheetLaw_isProbabilityMeasure (by positivity : 0 ≤ 2 * d)
    (axialProbability ρ hρ : Measure ℝ)
  exact hnorm.trans (mul_le_mul' le_rfl (hdom.trans (mul_le_mul' le_rfl
    (weight_lowRegion_bound hq₁ hq₂ hr hR hδ₀ hδ _ hv))))

def highRegion (v : Velocity) (R U : ℝ) : Set Coordinates :=
  ballRegion v R ∩ (WidthTails.incomingTail U ×ˢ univ)

theorem measurableSet_highRegion (v : Velocity) (R U : ℝ) : MeasurableSet (highRegion v R U) :=
  (measurableSet_ballRegion v R).inter ((WidthTails.measurableSet_incomingTail U).prod .univ)

theorem normalized_highRegion_bound {q d R U L : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8)
    (hR : 1 ≤ R) (hU : 0 < U) {v : Velocity} (hv : transverse v ≠ 0)
    {ρ : Measure ℝ} [IsProbabilityMeasure ρ] (hρ : AxialMoment ρ L) :
    normalizedMeasure (sheetLaw d ρ) q v (highRegion v R U) ≤
      ENNReal.ofReal tiltConstant * (ENNReal.ofReal ((8 * d ^ 2 / U ^ 2) * L) *
        ballBound q R) := by
  have hnorm := normalized_restriction_le (sheetLaw d ρ) q v
    (measurableSet_highRegion v R U) (measurableSet_highRegion v R U) (Subset.refl _)
    (B := 1) (by norm_num)
    (fun _ _ => Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _)))
  simp only [mul_one] at hnorm
  have he : ChartKernel.measure (tiltedSheet d ρ) (weightRatio q v) v (highRegion v R U) =
      ChartKernel.measure ((tiltedSheet d ρ).restrict (WidthTails.incomingTail U))
        (weightRatio q v) v (ballRegion v R) := by
    have := transverseTilt_finite hd hdmax
    have := axialTilt_finite hρ
    have : IsFiniteMeasure (tiltedSheet d ρ) := by
      rw [tiltedSheet_eq]
      infer_instance
    rw [measure_restrict_incoming _ _ _ (WidthTails.measurableSet_incomingTail U),
      Measure.restrict_apply (measurableSet_ballRegion v R)]
    rfl
  have hdom := measure_mono_incoming
    (WidthTails.tiltedSheet_transverse_tail hd hdmax hU hρ) (weightRatio q v) v (ballRegion v R)
  rw [ChartKernel.measure_smul, Measure.smul_apply, smul_eq_mul] at hdom
  change normalizedMeasure (sheetLaw d ρ) q v (highRegion v R U) ≤
    ENNReal.ofReal tiltConstant *
      ChartKernel.measure (tiltedSheet d ρ) (weightRatio q v) v (highRegion v R U) at hnorm
  rw [he] at hnorm
  exact hnorm.trans (mul_le_mul' le_rfl (hdom.trans (mul_le_mul' le_rfl
    (weight_ball_measure_bound hq₁ hq₂ (by positivity) hR hv (axialProbability ρ hρ)))))

end BoltzmannNonuniqueness.SmallInput

end

end

section

/-! # Vanishing input mass near the axis for thin sheets -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.UniformGain
open BoltzmannNonuniqueness.SmallInput

namespace BoltzmannNonuniqueness.SmallInputLimit

def lowBound (q L r R δ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal tiltConstant * (ENNReal.ofReal (4 * L) *
    (2 * ENNReal.ofReal (AffineSlices.rectangleConstant q δ δ /
      SmallInputGeometry.threshold r R)))

def highBound (q L R U d : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal tiltConstant * (ENNReal.ofReal ((8 * d ^ 2 / U ^ 2) * L) * ballBound q R)

theorem lowBound_tendsto {q : ℝ} (hq : q < 2) (L r R : ℝ) :
    Tendsto (lowBound q L r R) (nhds 0) (nhds 0) := by
  have hc : Continuous (fun δ : ℝ => AffineSlices.rectangleConstant q δ δ /
      SmallInputGeometry.threshold r R) := by
    unfold AffineSlices.rectangleConstant AffineSlices.intervalConstant
    have hp := Real.continuous_rpow_const (show 0 ≤ 2 - q by linarith)
    fun_prop
  have he : AffineSlices.rectangleConstant q 0 0 / SmallInputGeometry.threshold r R = 0 := by
    simp [AffineSlices.rectangleConstant, AffineSlices.intervalConstant,
      Real.zero_rpow (show 2 - q ≠ 0 by linarith)]
  have h := (ENNReal.continuous_ofReal.comp hc).tendsto 0
  rw [Function.comp_apply, he, ENNReal.ofReal_zero] at h
  have h₂ := ENNReal.Tendsto.const_mul h (a := 2) (Or.inr (by norm_num))
  have h₃ := ENNReal.Tendsto.const_mul h₂ (a := ENNReal.ofReal (4 * L))
    (Or.inr ENNReal.ofReal_ne_top)
  have h₄ := ENNReal.Tendsto.const_mul h₃ (a := ENNReal.ofReal tiltConstant)
    (Or.inr ENNReal.ofReal_ne_top)
  convert h₄ using 1 <;> first | (funext x; rfl) | simp only [mul_zero]

theorem highBound_tendsto (q L R U : ℝ) :
    Tendsto (highBound q L R U) (nhds 0) (nhds 0) := by
  have hc : Continuous (fun d : ℝ => (8 * d ^ 2 / U ^ 2) * L) := by fun_prop
  have h := (ENNReal.continuous_ofReal.comp hc).tendsto 0
  simp only [Function.comp_apply, zero_pow (by norm_num : 2 ≠ 0), mul_zero,
    zero_div, zero_mul, ENNReal.ofReal_zero] at h
  have h₂ := ENNReal.Tendsto.mul_const h (b := ballBound q R) (Or.inr (by
    unfold ballBound
    finiteness))
  have h₃ := ENNReal.Tendsto.const_mul h₂ (a := ENNReal.ofReal tiltConstant)
    (Or.inr ENNReal.ofReal_ne_top)
  convert h₃ using 1 <;> first | (funext x; rfl) | simp only [zero_mul, mul_zero]

def smallRegion (v : Velocity) (δ : ℝ) : Set Coordinates :=
  {y | ‖transverse (chart v y.1 y.2.1 y.2.2)‖ < δ}

/-- The thin-sheet small-input limit, uniformly in every output velocity
whose transverse component is at least `r`. -/
theorem uniform_small_input {q L r ε : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hr : 0 < r) (hε : 0 < ε) :
    ∃ δ η : ℝ, 0 < δ ∧ 0 < η ∧ ∀ (d : ℝ) (ρ : Measure ℝ) (_ : IsProbabilityMeasure ρ)
      (_ : 0 ≤ d) (_ : d ≤ min η (1 / 8)) (_ : AxialMoment ρ L)
      (v : Velocity) (_ : r ≤ ‖transverse v‖),
      normalizedMeasure (sheetLaw d ρ) q v (smallRegion v δ) ≤ ENNReal.ofReal ε := by
  have he : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 3) := ENNReal.ofReal_pos.mpr (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((SheetTightness.tendsto_tailBound q L).eventually (gt_mem_nhds he))
  let R : ℝ := 2 * ((N : ℝ) + 1)
  have hR : 1 ≤ R := by dsimp [R]; have := Nat.cast_nonneg (α := ℝ) N; linarith
  obtain ⟨s, hs, hsmall⟩ := Metric.eventually_nhds_iff.mp
    ((lowBound_tendsto hq₂ L r R).eventually (gt_mem_nhds he))
  obtain ⟨t, ht, hthin⟩ := Metric.eventually_nhds_iff.mp
    ((highBound_tendsto q L R (r / 4)).eventually (gt_mem_nhds he))
  let δ : ℝ := min (s / 2) (r / 6)
  have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
  have hδr : δ < r / 3 := (min_le_right _ _).trans_lt (by linarith)
  have hδs : dist δ 0 < s := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδpos]
    exact (min_le_left _ _).trans_lt (by linarith)
  refine ⟨δ, t / 2, hδpos, by linarith, ?_⟩
  intro d ρ hprob hd hdmax hρ v hv
  have hdthin : dist d 0 < t := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hd]
    exact (hdmax.trans (min_le_left _ _)).trans_lt (by linarith)
  have hvne : transverse v ≠ 0 := norm_pos_iff.mp (hr.trans_le hv)
  have hsub : smallRegion v δ ⊆ SheetTightness.tailRegion v N ∪
      (lowRegion v r R δ ∪ highRegion v R (r / 4)) := by
    intro y hy
    by_cases hh : R < radius v y
    · exact Or.inl hh
    · have hb : y ∈ ballRegion v R :=
        (le_add_of_nonneg_left (norm_nonneg y.1)).trans (le_of_not_gt hh)
      by_cases hp : ‖transverse y.1‖ ≤ r / 4
      · exact Or.inr (Or.inl ⟨⟨hb, hy⟩, hp, mem_univ _⟩)
      · exact Or.inr (Or.inr ⟨hb, lt_of_not_ge hp, mem_univ _⟩)
  apply (measure_mono hsub).trans
  apply (measure_union_le _ _).trans
  apply (add_le_add le_rfl (measure_union_le _ _)).trans
  calc
    _ ≤ SheetTightness.tailBound q L N + (lowBound q L r R δ + highBound q L R (r / 4) d) :=
      add_le_add (SheetTightness.normalized_tail_bound hq₁ hq₂ hd
        (hdmax.trans (min_le_right _ _)) hvne hρ N)
        (add_le_add (normalized_lowRegion_bound hq₁ hq₂ hd (hdmax.trans (min_le_right _ _))
          hr (by linarith) hδpos.le hδr hv hρ)
          (normalized_highRegion_bound hq₁ hq₂ hd (hdmax.trans (min_le_right _ _)) hR
            (by linarith) hvne hρ))
    _ ≤ ENNReal.ofReal (ε / 3) + (ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3)) :=
      add_le_add (hN N le_rfl).le (add_le_add (hsmall hδs).le (hthin hdthin).le)
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith),
        ← ENNReal.ofReal_add (by linarith) (by linarith)]
      congr 1
      ring

end BoltzmannNonuniqueness.SmallInputLimit

end

end

section

/-! # Uniform smallness of the first kernel makes a bounded finite gain chain small -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.PositiveIteration

theorem five_tendsto_of_small_first_mass {a T : ℝ}
    (K : ℕ → Kernel KineticPhase Velocity) {C B : ℝ≥0∞} (hC : C ≠ ∞) (hB : B ≠ ∞)
    (hK : ∀ n y, y.1.1 ∈ Icc a T → K n y univ ≤ C)
    {f : ℕ → KineticPhase → ℝ≥0∞} (hf : ∀ n y, y.1.1 ∈ Icc a T → f n y ≤ B)
    (z : ℕ → KineticPhase) (hz : ∀ n, (z n).1.1 ∈ Icc a T)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ s ∈ Icc a (z n).1.1,
      K n (flight (z n) s) univ ≤ ENNReal.ofReal ε) :
    Tendsto (fun n => iterate a (K n) (f n) 5 (z n)) atTop (𝓝 0) := by
  let Δ := ENNReal.ofReal (T-a)
  let D := B*(C*Δ)^4
  have hD : D ≠ ∞ := ENNReal.mul_ne_top hB
    (ENNReal.pow_ne_top (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top))
  have ht (n y) (hy : y.1.1 ∈ Icc a T) : iterate a (K n) (f n) 4 y ≤ D :=
    iterate_uniform_bound _ (hK n) (hf n) 4 y hy
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨e,he,heε⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (ENNReal.mul_ne_top hD ENNReal.ofReal_ne_top : D*Δ ≠ ∞) hε.ne'
  filter_upwards [hsmall e (NNReal.coe_pos.mpr he)] with n hn
  change step a (K n) (iterate a (K n) (f n) 4) (z n) ≤ ε
  unfold step
  calc
    _ ≤ ∫⁻ _s in Ioc a (z n).1.1, D*(e:ℝ≥0∞) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hsT : s ∈ Icc a T := ⟨hs.1.le,hs.2.trans (hz n).2⟩
      calc
        _ ≤ ∫⁻ _w, D ∂K n (flight (z n) s) := lintegral_mono (fun _ => ht n _ hsT)
        _ = D*K n (flight (z n) s) univ := by rw [lintegral_const,mul_comm]
        _ ≤ D*(e:ℝ≥0∞) := by
          apply mul_le_mul' le_rfl
          simpa only [ENNReal.ofReal_coe_nnreal] using hn s ⟨hs.1.le,hs.2⟩
    _ ≤ D*(e:ℝ≥0∞)*Δ := by
      rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioc]
      exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (sub_le_sub_right (hz n).2 a))
    _ = (e:ℝ≥0∞)*(D*Δ) := by ring
    _ ≤ ε := heε.le

end BoltzmannNonuniqueness.PositiveIteration

end

end

end OAI
