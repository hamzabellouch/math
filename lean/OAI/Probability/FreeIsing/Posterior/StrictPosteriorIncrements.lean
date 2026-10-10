import OAI.Probability.FreeIsing.Conditioning.StrictPosteriorInformation
import OAI.Probability.FreeIsing.Gibbs.CovarianceWindowEnergy
import OAI.Probability.FreeIsing.Martingales.TransformL2

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology BigOperators
namespace Problem367

theorem HasFreeIsingLaw.finiteGibbsSpinMean_brownian_strict_secondMoment_sub
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    {s t : ℝ≥0} (hst : s ≤ t) (v : TreeVertex d) (n : ℕ) :
    (∫ p, finiteGibbsSpinMean beta v n
      (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) -
    (∫ p, finiteGibbsSpinMean beta v n
      (fun i => (s : ℝ) * spinSign (p.1 i) + B i s (p.2 i)) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) ≤ strictInformationCoefficient d beta * ((t : ℝ) - s) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let P := (volume.restrict (Ioc (s : ℝ) t)).prod (μ.prod (Measure.infinitePi ν))
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
  have hmass : P.real univ = (t : ℝ) - s := by
    simp [P, measureReal_def, Measure.prod_apply, Real.volume_Ioc, sub_nonneg.mpr (show (s : ℝ) ≤ t from hst)]
  rw [hmass] at hs
  have he := hμ.finiteGibbsCovariance_windowEnergy_eq ν hB hmB hcB v n s.coe_nonneg
    (show (s : ℝ) ≤ t from hst)
  have hX (r : ℝ≥0) (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) :
      brownianIsingObservationR B ((r : ℝ), p) =
        (fun i => (r : ℝ) * spinSign (p.1 i) + B i r (p.2 i)) := by
    funext i
    change (r : ℝ) * spinSign (p.1 i) + B i (r : ℝ).toNNReal (p.2 i) = _
    rw [Real.toNNReal_coe]
  have he' : (∑' w, F w) = (∫ p, finiteGibbsSpinMean beta v n
      (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) -
      (∫ p, finiteGibbsSpinMean beta v n
        (fun i => (s : ℝ) * spinSign (p.1 i) + B i s (p.2 i)) ^ 2
        ∂μ.prod (Measure.infinitePi ν)) := by
    simpa only [F, P, hX] using he
  rw [he'] at hs
  simpa only [strictInformationCoefficient, mul_comm] using hs

theorem HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_strict_secondMoment_sub
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    {s t : ℝ≥0} (hst : s ≤ t) (v : TreeVertex d) :
    (∫ p, infiniteGibbsSpinMean beta v
      (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) -
    (∫ p, infiniteGibbsSpinMean beta v
      (fun i => (s : ℝ) * spinSign (p.1 i) + B i s (p.2 i)) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) ≤ strictInformationCoefficient d beta * ((t : ℝ) - s) := by
  exact le_of_tendsto
    ((hμ.finiteGibbsSpinMean_brownian_tendsto_integral_sq ν hB hmB t v).sub
      (hμ.finiteGibbsSpinMean_brownian_tendsto_integral_sq ν hB hmB s v))
    (Eventually.of_forall fun n =>
      hμ.finiteGibbsSpinMean_brownian_strict_secondMoment_sub hb hstrict ν hB hmB hcB hst v n)

theorem HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_increment_energy_eq
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    {s t : ℝ≥0} (hst : s ≤ t) (v : TreeVertex d) :
    (∫ p, (infiniteGibbsSpinMean beta v
      (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) -
        infiniteGibbsSpinMean beta v
      (fun i => (s : ℝ) * spinSign (p.1 i) + B i s (p.2 i))) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) =
    (∫ p, infiniteGibbsSpinMean beta v
      (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) -
    (∫ p, infiniteGibbsSpinMean beta v
      (fun i => (s : ℝ) * spinSign (p.1 i) + B i s (p.2 i)) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let P := μ.prod (Measure.infinitePi ν)
  let F := arrayObservationFiltration B hmB
    (fun (sigma : TreeVertex d → IsingSpin) i => spinSign (sigma i)) measurable_spinSign_array
  let M := fun r : ℝ≥0 => fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
    infiniteGibbsSpinMean beta v
      (fun i => (r : ℝ) * spinSign (p.1 i) + B i r (p.2 i))
  let Y := fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) => spinSign (p.1 v)
  have hce (r : ℝ≥0) : M r =ᵐ[P] P[Y | F r] := by
    have h := hμ.infiniteGibbsSpinMean_eq_brownian_past ν hB hmB r v
    simpa only [M, P, Y, F, arrayObservationFiltration, arrayNaturalFiltration_eq_comap,
      plantedArrayObservation, add_comm] using h
  have hM2 (r : ℝ≥0) : MemLp (M r) 2 P := by
    apply MemLp.of_bound (C := 1)
    · apply Measurable.aestronglyMeasurable
      apply (measurable_infiniteGibbsSpinMean beta v).comp
      apply Measurable.of_eval
      intro i
      exact (measurable_const.mul ((measurable_of_finite spinSign).comp
        ((measurable_pi_apply i).comp measurable_fst))).add
        ((hmB i r).comp ((measurable_pi_apply i).comp measurable_snd))
    · exact Eventually.of_forall fun p => by
        simpa only [M, Real.norm_eq_abs] using infiniteGibbsSpinMean_abs_le_one beta v
          (fun i => (r : ℝ) * spinSign (p.1 i) + B i r (p.2 i))
  have he := MartingaleTransformL2.integral_sq_increment_eq
    (martingale_condExp Y F P) hst ((memLp_congr_ae (hce s)).mp (hM2 s)) ((memLp_congr_ae (hce t)).mp (hM2 t))
  change (∫ p, (M t p - M s p) ^ 2 ∂P) =
    (∫ p, M t p ^ 2 ∂P) - ∫ p, M s p ^ 2 ∂P
  calc
    _ = ∫ p, (P[Y | F t] p - P[Y | F s] p) ^ 2 ∂P :=
      integral_congr_ae (((hce t).sub (hce s)).fun_comp (fun x : ℝ => x ^ 2))
    _ = _ := he
    _ = _ := by
      exact congrArg₂ (fun x y : ℝ => x - y)
        (integral_congr_ae ((hce t).symm.fun_comp (fun x : ℝ => x ^ 2)))
        (integral_congr_ae ((hce s).symm.fun_comp (fun x : ℝ => x ^ 2)))

theorem HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_strict_increment_bound
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    {s t : ℝ≥0} (hst : s ≤ t) (v : TreeVertex d) :
    (∫ p, (infiniteGibbsSpinMean beta v
      (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) -
        infiniteGibbsSpinMean beta v
      (fun i => (s : ℝ) * spinSign (p.1 i) + B i s (p.2 i))) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) ≤ strictInformationCoefficient d beta * ((t : ℝ) - s) := by
  rw [hμ.infiniteGibbsSpinMean_brownian_increment_energy_eq ν hB hmB hst v]
  exact hμ.infiniteGibbsSpinMean_brownian_strict_secondMoment_sub hb hstrict ν hB hmB hcB hst v

namespace IsingConditionalCopyBounds
open IsingObservationInnovation IsingObservationFactor

theorem posterior_strict_increment_bound
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1)
    {s t : ℝ≥0} (hst : s ≤ t) (v : TreeVertex d) :
    (∫ x, (posterior beta v t x - posterior beta v s x) ^ 2 ∂observationLaw μ) ≤
      strictInformationCoefficient d beta * ((t : ℝ) - s) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hm (r : ℝ≥0) : Measurable (posterior beta v r) :=
    (measurable_infiniteGibbsSpinMean beta v).comp
      (Measurable.of_eval (fun i => measurable_evaluation i r))
  have h := hμ.infiniteGibbsSpinMean_brownian_strict_increment_bound hb hstrict
    (fun _ => uniform01) (fun _ => WienerSampler.sample_isBrownianReal.toIsPreBrownianReal)
    (fun _ r => WienerSampler.measurable_sample_eval.comp
      (measurable_const.prodMk measurable_id))
    (fun _ u => (WienerSampler.sample u).continuous) hst v
  have hp (r : ℝ≥0) (p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) :
      posterior beta v r (uniformObservation p) =
        infiniteGibbsSpinMean beta v
          (fun i => (r : ℝ) * spinSign (p.1 i) + WienerSampler.sample (p.2 i) r) := by
    apply congrArg (infiniteGibbsSpinMean beta v)
    funext i
    exact add_comm _ _
  change (∫ x, ((posterior beta v t - posterior beta v s) x) ^ 2 ∂observationLaw μ) ≤ _
  rw [observationLaw, integral_map measurable_uniformObservation.aemeasurable
    (((hm t).sub (hm s)).pow_const 2).aestronglyMeasurable]
  simpa only [Pi.sub_apply, hp, labelMeasure] using h

end IsingConditionalCopyBounds
end Problem367

end

end OAI
