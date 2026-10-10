import OAI.MathematicalPhysics.Boltzmann.Branching.ChartPointLift
import Mathlib.Analysis.SpecialFunctions.Exp

namespace OAI

/-!
# Uniform elementary-sheet gain estimates

The incoming exponential tilt and the Gaussian in the companion velocity
are kept separate. All regions below refer to the complete normalized
kernel, including its singular velocity weight.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.UniformGain

def exponentialTilt (p : Velocity) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (2 * ‖p‖ ^ 2))

theorem measurable_exponentialTilt : Measurable exponentialTilt := by
  unfold exponentialTilt
  fun_prop

theorem measurable_weightRatio (q : ℝ) (v : Velocity) : Measurable (weightRatio q v) :=
  ((measurable_W q).div_const _).ennreal_ofReal

theorem ratio_bound {B : ℝ} (q : ℝ) (v p : Velocity) (z s : ℝ)
    (hn : normal v p ≠ 0)
    (hb : Real.exp (-‖companionVelocity p (chart v p z s) v‖ ^ 2) ≤ B) :
    H q (chart v p z s) / H q v ≤
      (tiltConstant * B) * Real.exp (2 * ‖p‖ ^ 2) *
        (W q (chart v p z s) / W q v) := by
  apply (chart_weight_ratio_le q v p z s hn).trans
  rw [sub_eq_add_neg, Real.exp_add]
  have hw : 0 ≤ W q (chart v p z s) / W q v :=
    div_nonneg (W_pos _ _).le (W_pos _ _).le
  calc
    _ ≤ tiltConstant * (Real.exp (2 * ‖p‖ ^ 2) * B) *
        (W q (chart v p z s) / W q v) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)) tiltConstant_pos.le) hw
    _ = _ := by ring

/-- The weight transfer can be applied on any measurable portion of the chart. -/
theorem normalized_restriction_le (c : Measure Velocity) (q : ℝ) (v : Velocity)
    {S T : Set Coordinates} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hST : S ⊆ T) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ y ∈ S,
      Real.exp (-‖companionVelocity y.1 (chart v y.1 y.2.1 y.2.2) v‖ ^ 2) ≤ B) :
    normalizedMeasure c q v S ≤ ENNReal.ofReal (tiltConstant * B) *
      ChartKernel.measure (c.withDensity exponentialTilt) (weightRatio q v) v T := by
  apply restriction_comparison c measurable_exponentialTilt (measurable_weightRatio q v)
    v _ hS hT
  intro y
  by_cases hy : y ∈ S
  · rw [indicator_of_mem hy, indicator_of_mem (hST hy)]
    by_cases hn : normal v y.1 = 0
    · simp [density, hn]
    · have hr := ENNReal.ofReal_le_ofReal
        (ratio_bound q v y.1 y.2.1 y.2.2 hn (hb y hy))
      have hc : 0 ≤ tiltConstant * B := mul_nonneg tiltConstant_pos.le hB
      rw [ENNReal.ofReal_mul (mul_nonneg hc (Real.exp_nonneg _)),
        ENNReal.ofReal_mul hc] at hr
      change 2 * ENNReal.ofReal _ * ENNReal.ofReal _ ≤
        ENNReal.ofReal (tiltConstant * B) *
          (exponentialTilt y.1 * (2 * ENNReal.ofReal _ * weightRatio q v _))
      have he := mul_le_mul_left hr (2 * ENNReal.ofReal (‖normal v y.1‖⁻¹))
      simpa only [exponentialTilt, weightRatio, mul_assoc, mul_left_comm, mul_comm] using he
  · rw [indicator_of_notMem hy]
    exact bot_le

theorem measurableSet_ballRegion (v : Velocity) (R : ℝ) : MeasurableSet (ballRegion v R) :=
  measurableSet_le ((measurable_point v).sub_const v).norm measurable_const

theorem weight_ball_measure_bound {q d R : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hd : 0 ≤ d) (hR : 1 ≤ R) {v : Velocity} (hv : transverse v ≠ 0)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    ChartKernel.measure (sheetLaw d ρ) (weightRatio q v) v (ballRegion v R) ≤
      2 * ENNReal.ofReal (GeometricSlice.geometricTotalConstant q * R ^ 2) := by
  rw [← region_eq_measure _ (measurable_weightRatio q v) v (measurableSet_ballRegion v R)]
  exact weight_ball_sheet_bound hq₁ hq₂ hd hR hv ρ

def ballBound (q R : ℝ) : ℝ≥0∞ :=
  2 * ENNReal.ofReal (GeometricSlice.geometricTotalConstant q * R ^ 2)

theorem tilted_ball_bound {q d R L : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8) (hR : 1 ≤ R)
    {v : Velocity} (hv : transverse v ≠ 0) {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρ : AxialMoment ρ L) :
    ChartKernel.measure (tiltedSheet d ρ) (weightRatio q v) v (ballRegion v R) ≤
      ENNReal.ofReal (4 * L) * ballBound q R := by
  have h := (measure_mono_incoming (tiltedSheet_le_probability hd hdmax hρ)
    (weightRatio q v) v) (ballRegion v R)
  rw [measure_smul, Measure.smul_apply, smul_eq_mul] at h
  exact h.trans (mul_le_mul' le_rfl
    (weight_ball_measure_bound hq₁ hq₂ (by positivity) hR hv (axialProbability ρ hρ)))

theorem tilted_tail_ball_bound {q d R L u : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8) (hR : 1 ≤ R) (hu : 0 ≤ u)
    {v : Velocity} (hv : transverse v ≠ 0) {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρ : AxialMoment ρ L) :
    ChartKernel.measure ((tiltedSheet d ρ).restrict {p : Velocity | u < ‖p‖})
      (weightRatio q v) v (ballRegion v R) ≤
        tailCoefficient L u * (ballBound q R + ballBound q R) := by
  have := sheetLaw_isProbabilityMeasure (by positivity : 0 ≤ 2 * d)
    (axialProbability ρ hρ : Measure ℝ)
  have := sheetLaw_isProbabilityMeasure (by positivity : 0 ≤ 2 * d)
    (axialTailProbability ρ hρ (by positivity : 0 ≤ u / 2) : Measure ℝ)
  have h := (measure_mono_incoming (tiltedSheet_tail_le hd hdmax hρ hu)
    (weightRatio q v) v) (ballRegion v R)
  rw [measure_smul, measure_add, Measure.smul_apply, Measure.add_apply, smul_eq_mul] at h
  exact h.trans (mul_le_mul' le_rfl (add_le_add
    (weight_ball_measure_bound hq₁ hq₂ (by positivity) hR hv (axialProbability ρ hρ))
    (weight_ball_measure_bound hq₁ hq₂ (by positivity) hR hv
      (axialTailProbability ρ hρ (by positivity : 0 ≤ u / 2)))))

theorem normalized_ball_bound {q d R L : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8) (hR : 1 ≤ R)
    {v : Velocity} (hv : transverse v ≠ 0) {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρ : AxialMoment ρ L) :
    normalizedMeasure (sheetLaw d ρ) q v (ballRegion v R) ≤
      ENNReal.ofReal tiltConstant * ENNReal.ofReal (4 * L) * ballBound q R := by
  have h := normalized_restriction_le (sheetLaw d ρ) q v
    (measurableSet_ballRegion v R) (measurableSet_ballRegion v R) (Subset.refl _)
    (B := 1) (by norm_num) (fun _ _ => Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _)))
  simp only [mul_one] at h
  exact h.trans ((mul_le_mul' le_rfl (tilted_ball_bound hq₁ hq₂ hd hdmax hR hv hρ)).trans_eq
    (mul_assoc _ _ _).symm)

def radius (v : Velocity) (y : Coordinates) : ℝ :=
  ‖y.1‖ + ‖chart v y.1 y.2.1 y.2.2 - v‖

def shell (v : Velocity) (R : ℝ) : Set Coordinates :=
  {y | R < radius v y ∧ radius v y ≤ 2 * R}

def incomingTail (u : ℝ) : Set Velocity := {p | u < ‖p‖}

def companionTail (v : Velocity) (u : ℝ) : Set Coordinates :=
  {y | u < ‖companionVelocity y.1 (chart v y.1 y.2.1 y.2.2) v‖}

theorem measurable_radius (v : Velocity) : Measurable (radius v) :=
  measurable_fst.norm.add (((measurable_point v).sub_const v).norm)

theorem measurableSet_shell (v : Velocity) (R : ℝ) : MeasurableSet (shell v R) :=
  (measurableSet_lt measurable_const (measurable_radius v)).inter
    (measurableSet_le (measurable_radius v) measurable_const)

theorem measurableSet_incomingTail (u : ℝ) : MeasurableSet (incomingTail u) :=
  measurableSet_lt measurable_const measurable_norm

theorem measurableSet_companionTail (v : Velocity) (u : ℝ) :
    MeasurableSet (companionTail v u) := by
  unfold companionTail companionVelocity
  exact measurableSet_lt measurable_const
    ((measurable_fst.add (measurable_point v)).sub_const v).norm

theorem shell_subset_ball (v : Velocity) (R : ℝ) : shell v R ⊆ ballRegion v (2 * R) := by
  intro y hy
  have hp := norm_nonneg y.1
  exact le_trans (le_add_of_nonneg_left hp) hy.2

theorem shell_subset_union (v : Velocity) (R : ℝ) :
    shell v R ⊆ (shell v R ∩ (incomingTail (R / 4) ×ˢ univ)) ∪
      (shell v R ∩ companionTail v (R / 2)) := by
  intro y hy
  rcases shell_alternative y.1 (chart v y.1 y.2.1 y.2.2 - v) hy.1 with hp | hw
  · exact Or.inl ⟨hy, hp, mem_univ _⟩
  · exact Or.inr ⟨hy, by simpa only [companionTail, mem_ofPred_eq,
      companionVelocity, add_sub_assoc] using hw⟩

theorem normalized_cold_shell_bound {q d R L : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8) (hR : 1 ≤ R)
    {v : Velocity} (hv : transverse v ≠ 0) {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρ : AxialMoment ρ L) :
    normalizedMeasure (sheetLaw d ρ) q v
      (shell v R ∩ (incomingTail (R / 4) ×ˢ univ)) ≤
      ENNReal.ofReal tiltConstant * tailCoefficient L (R / 4) *
        (ballBound q (2 * R) + ballBound q (2 * R)) := by
  have := sheetLaw_isProbabilityMeasure hd ρ
  rw [← Measure.restrict_apply (measurableSet_shell v R),
    ← normalized_restrict_incoming _ q v (measurableSet_incomingTail (R / 4))]
  have h := normalized_restriction_le ((sheetLaw d ρ).restrict (incomingTail (R / 4))) q v
    (measurableSet_shell v R) (measurableSet_ballRegion v (2 * R))
    (shell_subset_ball v R) (B := 1) (by norm_num)
    (fun _ _ => Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _)))
  simp only [mul_one] at h
  rw [← restrict_withDensity (measurableSet_incomingTail (R / 4))] at h
  exact h.trans ((mul_le_mul' le_rfl
    (tilted_tail_ball_bound hq₁ hq₂ hd hdmax (by linarith) (by positivity) hv hρ)).trans_eq
      (mul_assoc _ _ _).symm)

theorem normalized_hot_shell_bound {q d R L : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8) (hR : 1 ≤ R)
    {v : Velocity} (hv : transverse v ≠ 0) {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρ : AxialMoment ρ L) :
    normalizedMeasure (sheetLaw d ρ) q v (shell v R ∩ companionTail v (R / 2)) ≤
      ENNReal.ofReal (tiltConstant * Real.exp (-R ^ 2 / 4)) *
        ENNReal.ofReal (4 * L) * ballBound q (2 * R) := by
  have h := normalized_restriction_le (sheetLaw d ρ) q v
    ((measurableSet_shell v R).inter (measurableSet_companionTail v (R / 2)))
    (measurableSet_ballRegion v (2 * R))
    (fun y hy => shell_subset_ball v R hy.1) (Real.exp_nonneg (-R ^ 2 / 4))
    (fun y hy => gaussian_shell_decay (by linarith : 0 ≤ R) hy.2.le)
  exact h.trans ((mul_le_mul' le_rfl
    (tilted_ball_bound hq₁ hq₂ hd hdmax (by linarith) hv hρ)).trans_eq
      (mul_assoc _ _ _).symm)

theorem normalized_shell_bound_raw {q d R L : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8) (hR : 1 ≤ R)
    {v : Velocity} (hv : transverse v ≠ 0) {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρ : AxialMoment ρ L) :
    normalizedMeasure (sheetLaw d ρ) q v (shell v R) ≤
      ENNReal.ofReal tiltConstant * tailCoefficient L (R / 4) *
        (ballBound q (2 * R) + ballBound q (2 * R)) +
      ENNReal.ofReal (tiltConstant * Real.exp (-R ^ 2 / 4)) *
        ENNReal.ofReal (4 * L) * ballBound q (2 * R) := by
  calc
    _ ≤ normalizedMeasure (sheetLaw d ρ) q v
        ((shell v R ∩ (incomingTail (R / 4) ×ˢ univ)) ∪
          (shell v R ∩ companionTail v (R / 2))) := measure_mono (shell_subset_union v R)
    _ ≤ _ := (measure_union_le _ _).trans (add_le_add
      (normalized_cold_shell_bound hq₁ hq₂ hd hdmax hR hv hρ)
      (normalized_hot_shell_bound hq₁ hq₂ hd hdmax hR hv hρ))

def shellConstant (q L : ℝ) : ℝ :=
  96 * tiltConstant * GeometricSlice.geometricTotalConstant q * L

theorem geometricTotalConstant_nonneg {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) :
    0 ≤ GeometricSlice.geometricTotalConstant q := by
  unfold GeometricSlice.geometricTotalConstant
  exact mul_nonneg (by positivity) (GeometricSlice.geometricConstant_pos hq₁ hq₂).le

theorem shellConstant_nonneg {q L : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hL : 0 ≤ L) :
    0 ≤ shellConstant q L := by
  unfold shellConstant
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) tiltConstant_pos.le)
    (geometricTotalConstant_nonneg hq₁ hq₂)) hL

theorem shell_coefficient_bound {q L R : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hL : 0 ≤ L) :
    ENNReal.ofReal tiltConstant * tailCoefficient L (R / 4) *
        (ballBound q (2 * R) + ballBound q (2 * R)) +
      ENNReal.ofReal (tiltConstant * Real.exp (-R ^ 2 / 4)) *
        ENNReal.ofReal (4 * L) * ballBound q (2 * R) ≤
      ENNReal.ofReal (shellConstant q L * R ^ 2 * Real.exp (-(3 / 32) * R ^ 2)) := by
  have hC := geometricTotalConstant_nonneg hq₁ hq₂
  have ht := tiltConstant_pos.le
  have htwo : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  unfold ballBound tailCoefficient
  rw [← htwo]
  repeat first
    | rw [← ENNReal.ofReal_mul (by positivity)]
    | rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have he : Real.exp (-R ^ 2 / 4) ≤ Real.exp (-(3 / 32) * R ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg R]
  rw [show -(3 / 2) * (R / 4) ^ 2 = -(3 / 32) * R ^ 2 by ring]
  calc
    _ = (64 * tiltConstant * GeometricSlice.geometricTotalConstant q * L * R ^ 2) *
          Real.exp (-(3 / 32) * R ^ 2) +
        (32 * tiltConstant * GeometricSlice.geometricTotalConstant q * L * R ^ 2) *
          Real.exp (-R ^ 2 / 4) := by ring
    _ ≤ (64 * tiltConstant * GeometricSlice.geometricTotalConstant q * L * R ^ 2) *
          Real.exp (-(3 / 32) * R ^ 2) +
        (32 * tiltConstant * GeometricSlice.geometricTotalConstant q * L * R ^ 2) *
          Real.exp (-(3 / 32) * R ^ 2) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left he
        (by positivity : 0 ≤ 32 * tiltConstant *
          GeometricSlice.geometricTotalConstant q * L * R ^ 2))
    _ = _ := by unfold shellConstant; ring

/-- The full normalized kernel has a uniform Gaussian bound on every shell. -/
theorem normalized_shell_bound {q d R L : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8) (hR : 1 ≤ R)
    {v : Velocity} (hv : transverse v ≠ 0) {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρ : AxialMoment ρ L) :
    normalizedMeasure (sheetLaw d ρ) q v (shell v R) ≤
      ENNReal.ofReal (shellConstant q L * R ^ 2 * Real.exp (-(3 / 32) * R ^ 2)) :=
  (normalized_shell_bound_raw hq₁ hq₂ hd hdmax hR hv hρ).trans
    (shell_coefficient_bound hq₁ hq₂ hρ.nonneg)

end BoltzmannNonuniqueness.UniformGain

end

end OAI
