import OAI.MathematicalPhysics.Boltzmann.Branching.SlopedChart

namespace OAI

section

/-! # Decay of truncated chart measures at large axial output -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.SlopedChart

namespace BoltzmannNonuniqueness.LargeOutputSlices

theorem one_le_weight (q : ℝ) (v : Velocity) : 1 ≤ W q v := by
  unfold W singularity
  exact le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg _) _)

theorem ballChartFiber_threshold {q R A : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hR : 0 ≤ R) (hA : 0 < A) (v p : Velocity) (ha : A ≤ |axial (v - p)|) :
    ballChartFiber q v p R ≤ ENNReal.ofReal (AffineSlices.rectangleConstant q R R / A) := by
  by_cases hn : normal v p = 0
  · simp [ballChartFiber, hn]
  have hapos : 0 < |axial (v - p)| := hA.trans_le ha
  apply (ballChartFiber_slope_bound hq₁ hq₂ hR v p hn (abs_pos.mp hapos)).trans
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_left (AffineSlices.rectangleConstant_nonneg hq₁ hq₂ hR hR) hA
  exact ha.trans (le_mul_of_one_le_left hapos.le (one_le_weight q v))

def boundedIncoming (U : ℝ) : Set Velocity := {p | ‖p‖ ≤ U}

def boundedBall (v : Velocity) (R U : ℝ) : Set Coordinates :=
  ballRegion v R ∩ (boundedIncoming U ×ˢ univ)

theorem measurableSet_boundedIncoming (U : ℝ) : MeasurableSet (boundedIncoming U) :=
  measurableSet_le measurable_norm measurable_const

theorem measurableSet_boundedBall (v : Velocity) (R U : ℝ) : MeasurableSet (boundedBall v R U) :=
  (UniformGain.measurableSet_ballRegion v R).inter ((measurableSet_boundedIncoming U).prod .univ)

theorem axial_mismatch_lower {U A : ℝ} (v p : Velocity)
    (hv : U + A ≤ |axial v|) (hp : ‖p‖ ≤ U) : A ≤ |axial (v - p)| := by
  have htri : |axial v| ≤ |axial (v - p)| + |axial p| := by
    rw [axial_sub]
    simpa only [sub_add_cancel] using abs_add_le (axial v - axial p) (axial p)
  have habs : |axial p| ≤ ‖p‖ := by
    have h := norm_sq_split p
    nlinarith [sq_abs (axial p), sq_nonneg ‖transverse p‖, abs_nonneg (axial p), norm_nonneg p]
  linarith

theorem weight_boundedBall_bound {q R U A : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hR : 0 ≤ R) (hA : 0 < A) (c : Measure Velocity) [IsProbabilityMeasure c]
    {v : Velocity} (hv : U + A ≤ |axial v|) :
    ChartKernel.measure c (weightRatio q v) v (boundedBall v R U) ≤
      2 * ENNReal.ofReal (AffineSlices.rectangleConstant q R R / A) := by
  have he : ChartKernel.measure c (weightRatio q v) v (boundedBall v R U) =
      ChartKernel.measure (c.restrict (boundedIncoming U)) (weightRatio q v) v (ballRegion v R) := by
    rw [measure_restrict_incoming c _ _ (measurableSet_boundedIncoming U),
      Measure.restrict_apply (UniformGain.measurableSet_ballRegion v R)]
    rfl
  rw [he, ← region_eq_measure _ (UniformGain.measurable_weightRatio q v) v
    (UniformGain.measurableSet_ballRegion v R)]
  change 2 * (∫⁻ p, ballChartFiber q v p R ∂c.restrict (boundedIncoming U)) ≤ _
  apply mul_le_mul' le_rfl
  have hb : (∫⁻ p, ballChartFiber q v p R ∂c.restrict (boundedIncoming U)) ≤
      ∫⁻ _p in boundedIncoming U, ENNReal.ofReal (AffineSlices.rectangleConstant q R R / A) ∂c := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (measurableSet_boundedIncoming U)] with p hp
    exact ballChartFiber_threshold hq₁ hq₂ hR hA v p (axial_mismatch_lower v p hv hp)
  apply hb.trans
  rw [lintegral_const, Measure.restrict_apply_univ]
  exact mul_le_of_le_one_right zero_le prob_le_one

end BoltzmannNonuniqueness.LargeOutputSlices

end

end

section

/-! # Uniform decay of the normalized kernel at large output velocity -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.UniformGain
open BoltzmannNonuniqueness.LargeOutputSlices

namespace BoltzmannNonuniqueness.LargeOutput

def axialConstant (q L R : ℝ) : ℝ :=
  tiltConstant * (4 * L) * (2 * AffineSlices.rectangleConstant q R R)

theorem axialConstant_nonneg {q L R : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hL : 0 ≤ L) (hR : 0 ≤ R) : 0 ≤ axialConstant q L R := by
  have := tiltConstant_pos
  have := AffineSlices.rectangleConstant_nonneg hq₁ hq₂ hR hR
  unfold axialConstant
  positivity

theorem normalized_boundedBall_bound {q d R U A L : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8)
    (hR : 0 ≤ R) (hA : 0 < A) {v : Velocity} (hv : U + A ≤ |axial v|)
    {ρ : Measure ℝ} [IsProbabilityMeasure ρ] (hρ : AxialMoment ρ L) :
    normalizedMeasure (sheetLaw d ρ) q v (boundedBall v R U) ≤
      ENNReal.ofReal (axialConstant q L R / A) := by
  have hnorm := normalized_restriction_le (sheetLaw d ρ) q v
    (measurableSet_boundedBall v R U) (measurableSet_boundedBall v R U) (Subset.refl _)
    (B := 1) (by norm_num)
    (fun _ _ => Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _)))
  simp only [mul_one] at hnorm
  have hdom := measure_mono_incoming (tiltedSheet_le_probability hd hdmax hρ)
    (weightRatio q v) v (boundedBall v R U)
  rw [ChartKernel.measure_smul, Measure.smul_apply, smul_eq_mul] at hdom
  have := sheetLaw_isProbabilityMeasure (by positivity : 0 ≤ 2 * d)
    (axialProbability ρ hρ : Measure ℝ)
  apply (hnorm.trans (mul_le_mul' le_rfl (hdom.trans (mul_le_mul' le_rfl
    (weight_boundedBall_bound hq₁ hq₂ hR hA _ hv))))).trans_eq
  have hC := AffineSlices.rectangleConstant_nonneg hq₁ hq₂ hR hR
  have hL := hρ.nonneg
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.ofReal_mul (show 0 ≤ 4 * L by positivity),
    ← ENNReal.ofReal_mul tiltConstant_pos.le]
  apply congrArg ENNReal.ofReal
  unfold axialConstant
  ring

def transverseConstant (q L R : ℝ) : ℝ :=
  tiltConstant * (4 * L) * 2 * (8 * R ^ 2) * TransverseAverage.expectationConstant q

theorem transverseConstant_nonneg (q : ℝ) {L : ℝ} (hL : 0 ≤ L) (R : ℝ) :
    0 ≤ transverseConstant q L R := by
  have := tiltConstant_pos
  have := TransverseAverage.expectationConstant_pos q
  unfold transverseConstant
  positivity

theorem normalized_awayBall_bound {q d R L : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8)
    (hR : 0 ≤ R) {v : Velocity} (hv : transverse v ≠ 0)
    {ρ : Measure ℝ} [IsProbabilityMeasure ρ] (hρ : AxialMoment ρ L) :
    normalizedMeasure (sheetLaw d ρ) q v (AxisInput.awayBall v R 1) ≤
      ENNReal.ofReal (transverseConstant q L R / ‖transverse v‖) := by
  apply (AxisInput.normalized_awayBall_bound hq₁ hq₂ hd hdmax hR (by norm_num) hv hρ).trans
  have hL := hρ.nonneg
  have he := TransverseAverage.expectationConstant_pos q
  have hr : 0 < ‖transverse v‖ := norm_pos_iff.mpr hv
  have hfrac : (1 + (1 : ℝ) ^ (-q)) / W q v ≤ 2 := by
    rw [Real.one_rpow]
    have hw := one_le_weight q v
    exact (div_le_iff₀ (W_pos q v)).mpr (by linarith)
  apply (mul_le_mul' le_rfl (mul_le_mul' le_rfl
    (mul_le_mul' (ENNReal.ofReal_le_ofReal hfrac) le_rfl))).trans_eq
  conv_lhs =>
    enter [2, 2, 2, 1, 1]
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num]
  repeat rw [← ENNReal.ofReal_mul (by positivity)]
  rw [← ENNReal.ofReal_mul tiltConstant_pos.le]
  apply congrArg ENNReal.ofReal
  unfold transverseConstant
  ring

theorem transverse_norm_le (v : Velocity) : ‖transverse v‖ ≤ ‖v‖ := by
  have h := norm_sq_split v
  nlinarith [sq_nonneg (axial v), norm_nonneg (transverse v), norm_nonneg v]

theorem ball_subset_away {R : ℝ} {v : Velocity} (hv : R + 1 ≤ ‖transverse v‖) :
    ballRegion v R ⊆ AxisInput.awayBall v R 1 := by
  intro y hy
  refine ⟨hy, ?_⟩
  have h := norm_sub_norm_le (transverse v) (transverse (chart v y.1 y.2.1 y.2.2))
  rw [← transverse_sub] at h
  have hs := transverse_norm_le (v - chart v y.1 y.2.1 y.2.2)
  rw [norm_sub_rev v] at hs
  change ‖chart v y.1 y.2.1 y.2.2 - v‖ ≤ R at hy
  change 1 ≤ ‖transverse (chart v y.1 y.2.1 y.2.2)‖
  linarith

/-- Uniform decay of the full kernel as the output velocity goes to infinity. -/
theorem uniform_large_output {q L ε : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ (d : ℝ) (ρ : Measure ℝ) (_ : IsProbabilityMeasure ρ)
      (_ : 0 ≤ d) (_ : d ≤ 1 / 8) (_ : AxialMoment ρ L)
      (v : Velocity) (_ : transverse v ≠ 0) (_ : M < ‖v‖),
      normalizedMeasure (sheetLaw d ρ) q v univ ≤ ENNReal.ofReal ε := by
  have he : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.mpr (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((SheetTightness.tendsto_tailBound q L).eventually (gt_mem_nhds he))
  let R : ℝ := 2 * ((N : ℝ) + 1)
  have hR : 0 < R := by dsimp [R]; positivity
  let A : ℝ := |axialConstant q L R| / (ε / 2) + 1
  let T : ℝ := R + 1 + |transverseConstant q L R| / (ε / 2) + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨T + (R + A), by positivity, ?_⟩
  intro d ρ hprob hd hdmax hρ v hv hvlarge
  have hsplit : T < ‖transverse v‖ ∨ R + A < |axial v| := by
    by_contra! hh
    have hn := norm_sq_split v
    nlinarith [sq_abs (axial v), norm_nonneg v, norm_nonneg (transverse v), abs_nonneg (axial v)]
  have hsub : (univ : Set Coordinates) ⊆ SheetTightness.tailRegion v N ∪ boundedBall v R R := by
    intro y _
    by_cases hh : R < radius v y
    · exact Or.inl hh
    · have hrad := le_of_not_gt hh
      change ‖y.1‖ + ‖chart v y.1 y.2.1 y.2.2 - v‖ ≤ R at hrad
      exact Or.inr ⟨by dsimp [ballRegion]; linarith [norm_nonneg y.1],
        by dsimp [boundedIncoming]; linarith [norm_nonneg (chart v y.1 y.2.1 y.2.2 - v)], mem_univ _⟩
  apply (measure_mono hsub).trans
  apply (measure_union_le _ _).trans
  have hb : normalizedMeasure (sheetLaw d ρ) q v (boundedBall v R R) ≤ ENNReal.ofReal (ε / 2) := by
    rcases hsplit with ht | ha
    · have hrlarge : R + 1 ≤ ‖transverse v‖ := by
        have hh := div_nonneg (abs_nonneg (transverseConstant q L R))
          (show 0 ≤ ε / 2 by linarith)
        dsimp [T] at ht
        linarith
      apply (measure_mono (show boundedBall v R R ⊆ AxisInput.awayBall v R 1 from
        fun _ hy => ball_subset_away hrlarge hy.1)).trans
      apply (normalized_awayBall_bound hq₁ hq₂ hd hdmax hR.le hv hρ).trans
      apply ENNReal.ofReal_le_ofReal
      apply (div_le_iff₀ (norm_pos_iff.mpr hv)).mpr
      have ht' : |transverseConstant q L R| / (ε / 2) < ‖transverse v‖ := by
        dsimp [T] at ht
        linarith
      have hc := (div_lt_iff₀ (by linarith : 0 < ε / 2)).mp ht'
      nlinarith [le_abs_self (transverseConstant q L R)]
    · apply (normalized_boundedBall_bound hq₁ hq₂ hd hdmax hR.le hA ha.le hρ).trans
      apply ENNReal.ofReal_le_ofReal
      apply (div_le_iff₀ hA).mpr
      have hc : |axialConstant q L R| < (ε / 2) * A := by
        dsimp [A]
        field_simp
        nlinarith
      exact (le_abs_self _).trans hc.le
  calc
    _ ≤ SheetTightness.tailBound q L N + ENNReal.ofReal (ε / 2) :=
      add_le_add (SheetTightness.normalized_tail_bound hq₁ hq₂ hd hdmax hv hρ N) hb
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add (hN N le_rfl).le le_rfl
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
      congr 1
      ring

end BoltzmannNonuniqueness.LargeOutput

end

end

end OAI
