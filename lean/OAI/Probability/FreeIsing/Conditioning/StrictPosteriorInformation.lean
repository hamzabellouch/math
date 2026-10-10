import OAI.Probability.FreeIsing.Gibbs.CovarianceStrictEnergy
import OAI.Probability.FreeIsing.Ising.CopyInformationBound
import OAI.Probability.FreeIsing.Ising.ObservationFactor

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology BigOperators

namespace Problem367

def strictInformationCoefficient (d : ℕ) (beta : ℝ) : ℝ :=
  1 + (d : ℝ) * Real.tanh beta ^ 2 /
    (1 - ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2)

theorem strictInformationCoefficient_pos {d : ℕ} {beta : ℝ}
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1) :
    0 < strictInformationCoefficient d beta := by
  have hden : 0 < 1 - ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 := by linarith
  unfold strictInformationCoefficient
  positivity

theorem HasFreeIsingLaw.finiteGibbsSpinMean_brownian_strict_secondMoment
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (t : ℝ≥0) (v : TreeVertex d) (n : ℕ) :
    (∫ p, finiteGibbsSpinMean beta v n
      (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) ≤ strictInformationCoefficient d beta * t := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let P := (volume.restrict (Ioc (0 : ℝ) t)).prod (μ.prod (Measure.infinitePi ν))
  let F := fun w : TreeVertex d => ∫ p,
    finiteGibbsCovariance beta v w n (brownianIsingObservationR B p) ^ 2 ∂P
  have hbound (w : TreeVertex d) :
      F w ≤ P.real univ * (Real.tanh beta ^ 2) ^ reducedWordDistance v.1 w.1 := by
    calc
      _ ≤ ∫ _p, (Real.tanh beta ^ reducedWordDistance v.1 w.1) ^ 2 ∂P := by
        apply integral_mono
          (integrable_finiteGibbsCovariance_sq beta v w n
            (measurable_brownianIsingObservationR hmB hcB)) (integrable_const _)
        intro p
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
          (finiteGibbsCovariance_abs_le_distance hb v w n (brownianIsingObservationR B p)) 2
      _ = _ := by
        rw [integral_const, smul_eq_mul]
        congr 1
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  obtain ⟨g, _, hd⟩ := exists_treeAut_to_root_distance v
  have hdist (w : TreeVertex d) :
      reducedWordDistance v.1 (g.toEquiv.symm w).1 = w.1.length := by
    simpa only [Equiv.apply_symm_apply] using (hd (g.toEquiv.symm w)).symm
  have hs := tsum_le_of_tree_radial_le
    (fun w => integral_nonneg (fun p => sq_nonneg
      (finiteGibbsCovariance beta v (g.toEquiv.symm w) n (brownianIsingObservationR B p))))
    (fun w => by simpa only [hdist] using hbound (g.toEquiv.symm w))
    (sq_nonneg (Real.tanh beta)) hstrict
  rw [g.toEquiv.symm.tsum_eq F] at hs
  have hmass : P.real univ = (t : ℝ) := by
    simp [P, measureReal_def, Measure.prod_apply, Real.volume_Ioc]
  rw [hmass] at hs
  have he := hμ.finiteGibbsCovariance_timeEnergy_eq ν hB hmB hcB v n t.coe_nonneg
  have hX (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) :
      brownianIsingObservationR B ((t : ℝ), p) =
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) := by
    funext i
    change (t : ℝ) * spinSign (p.1 i) + B i (t : ℝ).toNNReal (p.2 i) = _
    rw [Real.toNNReal_coe]
  have he' : (∑' w, F w) = ∫ p, finiteGibbsSpinMean beta v n
      (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) ^ 2
      ∂μ.prod (Measure.infinitePi ν) := by
    simpa only [F, P, hX] using he
  rw [he'] at hs
  simpa only [strictInformationCoefficient, mul_comm] using hs

theorem HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_strict_secondMoment
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (t : ℝ≥0) (v : TreeVertex d) :
    (∫ p, infiniteGibbsSpinMean beta v
      (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) ≤ strictInformationCoefficient d beta * t := by
  exact le_of_tendsto (hμ.finiteGibbsSpinMean_brownian_tendsto_integral_sq ν hB hmB t v)
    (Eventually.of_forall fun n =>
      hμ.finiteGibbsSpinMean_brownian_strict_secondMoment hb hstrict ν hB hmB hcB t v n)

namespace IsingConditionalCopyBounds

open IsingObservationInnovation IsingObservationFactor

theorem posteriorInformation_le_strict
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1)
    (t : ℝ≥0) (v : TreeVertex d) :
    posteriorInformation beta μ v t ≤ strictInformationCoefficient d beta * t := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hm : Measurable (posterior beta v t) :=
    (measurable_infiniteGibbsSpinMean beta v).comp
      (Measurable.of_eval (fun i => measurable_evaluation i t))
  have h := hμ.infiniteGibbsSpinMean_brownian_strict_secondMoment hb hstrict
    (fun _ => uniform01) (fun _ => WienerSampler.sample_isBrownianReal.toIsPreBrownianReal)
    (fun _ s => WienerSampler.measurable_sample_eval.comp
      (measurable_const.prodMk measurable_id))
    (fun _ u => (WienerSampler.sample u).continuous) t v
  have heq : posteriorInformation beta μ v t =
      ∫ p, infiniteGibbsSpinMean beta v
        (fun i => (t : ℝ) * spinSign (p.1 i) + WienerSampler.sample (p.2 i) t) ^ 2
        ∂μ.prod (labelMeasure d) := by
    rw [posteriorInformation, observationLaw,
      integral_map measurable_uniformObservation.aemeasurable (hm.pow_const 2).aestronglyMeasurable]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro p
    apply congrArg (fun y => infiniteGibbsSpinMean beta v y ^ 2)
    funext i
    exact add_comm _ _
  rw [heq]
  exact h

theorem canonical_fieldDifference_secondMoment_le_strict
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1)
    {T t : ℝ≥0} (ht : t ≤ T) (v : TreeVertex d) :
    (∫ q, fieldDifference beta v t q ^ 2 ∂copies beta μ) ≤
      (2 * (8 + 4 * (2 * (T : ℝ) + 2 * (d : ℝ) * beta) ^ 2) *
        strictInformationCoefficient d beta) * t := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) := inferInstance
  have h := fieldDifference_secondMoment_le_horizon_information hμ hb
    (ObservableDisintegration.compProd_kernel (observationLaw μ)
      (measurable_innovationMap beta)) ht v
  calc
    _ ≤ 2 * (8 + 4 * (2 * (T : ℝ) + 2 * (d : ℝ) * beta) ^ 2) *
        posteriorInformation beta μ v t := h
    _ ≤ 2 * (8 + 4 * (2 * (T : ℝ) + 2 * (d : ℝ) * beta) ^ 2) *
        (strictInformationCoefficient d beta * t) :=
      mul_le_mul_of_nonneg_left (posteriorInformation_le_strict hμ hb hstrict t v)
        (by positivity)
    _ = _ := by ring

end IsingConditionalCopyBounds

end Problem367

end

end OAI
