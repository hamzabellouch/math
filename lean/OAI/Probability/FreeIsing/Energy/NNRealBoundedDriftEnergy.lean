import OAI.Probability.FreeIsing.Estimates.NNRealArtanhFormula
import OAI.Probability.FreeIsing.Estimates.ProgressiveTimePrimitive
import OAI.Probability.FreeIsing.Martingales.BoundedMartingaleDriftEnergy
import OAI.Probability.FreeIsing.Trees.InnovationPathMap

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

namespace Problem367.NNRealBoundedDriftEnergy

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsFiniteMeasure μ] {F : Filtration ℝ≥0 mΩ}

theorem stronglyMeasurable_realExtension {X : ℝ≥0 → Ω → ℝ}
    (hX : IsStronglyProgressive F X) :
    StronglyMeasurable (fun p : ℝ × Ω => X p.1.toNNReal p.2) :=
  (stronglyMeasurable_joint_of_isStronglyProgressive hX).comp_measurable
    ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)

theorem integral_sq_of_bounded_process
    {M b : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {C D : ℝ}
    (hM : Martingale M F μ)
    (hprogM : IsStronglyProgressive F M) (hprogb : IsStronglyProgressive F b)
    (hbInt : Integrable (fun p : ℝ × Ω => b p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod μ))
    (hX : ∀ᵐ ω ∂μ, |M T ω + nnrealTimePrimitive b T ω| ≤ C)
    (hA : ∀ᵐ ω ∂μ, ∀ t ≤ T, |nnrealTimePrimitive b t ω| ≤ D) :
    Integrable (fun ω => (M T ω + nnrealTimePrimitive b T ω) ^ 2) μ ∧
      (∫ ω, (M T ω + nnrealTimePrimitive b T ω) ^ 2 ∂μ) =
        (∫ ω, M T ω ^ 2 ∂μ) +
          2 * ∫ s in (0 : ℝ)..(T : ℝ), ∫ ω,
            (M s.toNNReal ω + nnrealTimePrimitive b s.toNNReal ω) *
              b s.toNNReal ω ∂μ := by
  have hF := NNRealArtanhFormula.martingale_realExtension hM
  have hb : StronglyAdapted (NNRealArtanhFormula.realFiltration F)
      (fun t : ℝ => b t.toNNReal) := fun t => hprogb.stronglyAdapted t.toNNReal
  have hA' : ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ) (T : ℝ),
      |∫ s in (0 : ℝ)..t, b s.toNNReal ω| ≤ D := by
    filter_upwards [hA] with ω hω
    intro t ht
    have h := hω t.toNNReal (NNRealArtanhFormula.toNNReal_mem_Icc ht).2
    simpa only [nnrealTimePrimitive, Real.coe_toNNReal t ht.1] using h
  have h := MartingaleDriftEnergy.integral_sq_of_bounded_process T.coe_nonneg
    hF hb (stronglyMeasurable_realExtension hprogb) hbInt
    ((stronglyMeasurable_realExtension hprogM).mul
      (stronglyMeasurable_realExtension hprogb)).aestronglyMeasurable
    (by simpa only [Real.toNNReal_coe, nnrealTimePrimitive] using hX) hA'
  simp only [Real.toNNReal_coe] at h
  refine ⟨h.1, h.2.trans ?_⟩
  congr 2
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le T.coe_nonneg] at hs
  simp only [nnrealTimePrimitive, Real.coe_toNNReal s hs.1]

theorem integral_sq_of_bounded_process_compensated
    {M b q : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {C D : ℝ}
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - nnrealTimePrimitive q t ω) F μ)
    (hprogM : IsStronglyProgressive F M) (hprogb : IsStronglyProgressive F b)
    (hbInt : Integrable (fun p : ℝ × Ω => b p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod μ))
    (hqInt : Integrable (fun p : ℝ × Ω => q p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod μ))
    (hX : ∀ᵐ ω ∂μ, ∀ t ≤ T, |M t ω + nnrealTimePrimitive b t ω| ≤ C)
    (hA : ∀ᵐ ω ∂μ, ∀ t ≤ T, |nnrealTimePrimitive b t ω| ≤ D) :
    Integrable (fun ω => (M T ω + nnrealTimePrimitive b T ω) ^ 2) μ ∧
      (∫ ω, (M T ω + nnrealTimePrimitive b T ω) ^ 2 ∂μ) =
        (∫ ω, M 0 ω ^ 2 ∂μ) + ∫ s in (0 : ℝ)..(T : ℝ), ∫ ω,
          q s.toNNReal ω + 2 *
            ((M s.toNNReal ω + nnrealTimePrimitive b s.toNNReal ω) *
              b s.toNNReal ω) ∂μ := by
  obtain ⟨hInt, hsq⟩ := integral_sq_of_bounded_process hM hprogM hprogb hbInt
    (hX.mono (fun ω hω => hω T le_rfl)) hA
  have hqp : Integrable (nnrealTimePrimitive q T) μ := by
    change Integrable (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), q s.toNNReal ω) μ
    simpa only [intervalIntegral.integral_of_le T.coe_nonneg] using
      hqInt.integral_prod_right
  have hM2 : Integrable (fun ω => M T ω ^ 2) μ := by
    have hi := (hQ.integrable T).add hqp
    exact hi.congr (Eventually.of_forall (fun ω => sub_add_cancel _ _))
  have he := hQ.setIntegral_eq (show (0 : ℝ≥0) ≤ T from zero_le) MeasurableSet.univ
  simp only [Measure.restrict_univ] at he
  have hz (ω : Ω) : nnrealTimePrimitive q 0 ω = 0 := by simp [nnrealTimePrimitive]
  simp only [hz, sub_zero] at he
  rw [integral_sub hM2 hqp] at he
  have hqmean : (∫ ω, nnrealTimePrimitive q T ω ∂μ) =
      ∫ s in (0 : ℝ)..(T : ℝ), ∫ ω, q s.toNNReal ω ∂μ :=
    DiscrepancyEnergy.integral_timePrimitive ⟨T.coe_nonneg, le_rfl⟩ hqInt
  have henergy := stronglyMeasurable_realExtension
    (hprogM.add (isStronglyProgressive_nnrealTimePrimitive hprogb))
  have hprod : Integrable (fun p : ℝ × Ω =>
      (M p.1.toNNReal p.2 + nnrealTimePrimitive b p.1.toNNReal p.2) *
        b p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod μ) := by
    apply hbInt.bdd_mul henergy.aestronglyMeasurable
    have hbound : ∀ᵐ p ∂((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod μ),
        ∀ t ≤ T, |M t p.2 + nnrealTimePrimitive b t p.2| ≤ C :=
      Measure.quasiMeasurePreserving_snd.ae hX
    have hmem : ∀ᵐ p ∂((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod μ),
        p.1 ∈ Ioc (0 : ℝ) (T : ℝ) :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hbound, hmem] with p hp hpt
    simpa only [Real.norm_eq_abs] using hp p.1.toNNReal
      (NNRealArtanhFormula.toNNReal_mem_Icc ⟨hpt.1.le, hpt.2⟩).2
  have hadd : (∫ s in (0 : ℝ)..(T : ℝ), ∫ ω,
      q s.toNNReal ω + 2 *
        ((M s.toNNReal ω + nnrealTimePrimitive b s.toNNReal ω) * b s.toNNReal ω) ∂μ) =
      (∫ s in (0 : ℝ)..(T : ℝ), ∫ ω, q s.toNNReal ω ∂μ) +
        2 * ∫ s in (0 : ℝ)..(T : ℝ), ∫ ω,
          (M s.toNNReal ω + nnrealTimePrimitive b s.toNNReal ω) * b s.toNNReal ω ∂μ := by
    simp only [intervalIntegral.integral_of_le T.coe_nonneg]
    calc
      _ = ∫ s in Ioc (0 : ℝ) (T : ℝ),
          (∫ ω, q s.toNNReal ω ∂μ) + 2 * ∫ ω,
            (M s.toNNReal ω + nnrealTimePrimitive b s.toNNReal ω) * b s.toNNReal ω ∂μ := by
        apply integral_congr_ae
        filter_upwards [hqInt.prod_right_ae, hprod.prod_right_ae] with s hs hp
        rw [integral_add hs (hp.const_mul 2), integral_const_mul]
      _ = _ := by
        rw [integral_add hqInt.integral_prod_left (hprod.integral_prod_left.const_mul 2),
          integral_const_mul]
  refine ⟨hInt, ?_⟩
  rw [hadd, hsq]
  change (∫ ω, M 0 ω ^ 2 ∂μ) =
    (∫ ω, M T ω ^ 2 ∂μ) - (∫ ω, nnrealTimePrimitive q T ω ∂μ) at he
  rw [hqmean] at he
  linarith

end Problem367.NNRealBoundedDriftEnergy

end

end OAI
