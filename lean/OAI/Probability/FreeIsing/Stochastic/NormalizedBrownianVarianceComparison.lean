import OAI.Probability.FreeIsing.Energy.NormalizedInfiniteTimeEnergy
import OAI.Probability.FreeIsing.Gaussian.TreeResponseVarianceMixture

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace Problem367.NormalizedBrownianVarianceComparison

open GaussianTreeResponse

local instance : Nonempty IsingSpin := ⟨.neg⟩

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

lemma shiftedRow_eq_normalized (beta : ℝ) (D : Finset (TreeVertex d))
    (v w : D) (t : ℝ) (p : (TreeVertex d → IsingSpin) × (D → ℝ)) :
    shiftedRow beta D v (spinDrift t) (fun _ => 0) w p =
      FinitePosterior.normalizedFieldCovariance (finiteIsingEnergy beta D)
        (fun eta u => spinSign (eta u)) (fun eta => spinSign (eta v))
        (fun u => t * spinSign (p.1 u) + p.2 u) w := by
  classical
  simp only [shiftedRow, GaussianTreeResponse.finiteRow, ite_eq_left w.property]
  unfold response TreePathResponse.response TreePathResponse.covariance
    LeafGibbs.covariance TreePathResponse.mean
    FinitePosterior.normalizedFieldCovariance FinitePosterior.fieldCovariance
  simp only [extendFiniteSpin_apply D _ v, extendFiniteSpin_apply D _ w,
    GibbsLeaf.expectation_eq_fieldMean]
  have hx : D.restrict (fun u => spinDrift t p.1 u +
      Function.updateFinset (fun _ => (0 : ℝ)) D p.2 u) =
      (fun u : D => t * spinSign (p.1 u) + p.2 u) := by
    funext u
    simp [Finset.restrict, spinDrift, Function.updateFinset]
  rw [hx]

lemma shiftedRaw_eq_covariance (beta : ℝ) (D : Finset (TreeVertex d))
    (v w : D) (t : ℝ) (p : (TreeVertex d → IsingSpin) × (D → ℝ)) :
    GaussianTreeCovariance.finiteRow beta D v (spinDrift t p.1) (fun _ => 0) w p.2 =
      FinitePosterior.fieldCovariance (finiteIsingEnergy beta D)
        (fun eta u => spinSign (eta u)) (fun eta => spinSign (eta v))
        (fun u => t * spinSign (p.1 u) + p.2 u) w := by
  classical
  simp only [GaussianTreeCovariance.finiteRow, ite_eq_left w.property]
  unfold GaussianTreeCovariance.covariance LeafGibbs.covariance
    FinitePosterior.fieldCovariance
  simp only [extendFiniteSpin_apply D _ v, extendFiniteSpin_apply D _ w,
    GibbsLeaf.expectation_eq_fieldMean]
  have hx : D.restrict (fun u => spinDrift t p.1 u +
      Function.updateFinset (fun _ => (0 : ℝ)) D p.2 u) =
      (fun u : D => t * spinSign (p.1 u) + p.2 u) := by
    funext u
    simp [Finset.restrict, spinDrift, Function.updateFinset]
  rw [hx]

theorem varianceLower_mul_integral_normalized_sq_le_raw
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (ν : TreeVertex d → Measure Ω) {beta : ℝ} (hb : 0 ≤ beta)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v w : D)
    (hv : v.1.1 = []) {T : ℝ} (hT : 0 ≤ T) {t : ℝ≥0} (ht : (t : ℝ) ≤ T) :
    GaussianVarianceLower.varianceLower T (T + (d : ℝ) * beta) *
      (∫ p, finiteIsingBrownianNormalizedCovariance beta D v w B t p ^ 2
        ∂μ.prod (Measure.infinitePi ν)) ≤
      ∫ p, finiteIsingBrownianCovariance beta D v w B t p ^ 2
        ∂μ.prod (Measure.infinitePi ν) := by
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hbound (σ : TreeVertex d → IsingSpin) : |spinDrift (t : ℝ) σ v| ≤ T := by
    unfold spinDrift
    cases σ v <;> simpa [spinSign, abs_of_nonneg t.property] using ht
  have hc := varianceLower_mul_integral_shiftedRow_sq_le_raw μ hb (fun _ => t)
    hT hD v hv ht (spinDrift t) (measurable_spinDrift d t) hT hbound (fun _ => 0) w
  have hp := (MeasurePreserving.id μ).prod
    (finiteBrownianNoise_restrict_measurePreserving ν hB hmB D t)
  let f : ((TreeVertex d → IsingSpin) × (D → ℝ)) → ℝ := fun p =>
    FinitePosterior.normalizedFieldCovariance (finiteIsingEnergy beta D)
      (fun eta u => spinSign (eta u)) (fun eta => spinSign (eta v))
      (fun u => (t : ℝ) * spinSign (p.1 u) + p.2 u) w ^ 2
  let g : ((TreeVertex d → IsingSpin) × (D → ℝ)) → ℝ := fun p =>
    FinitePosterior.fieldCovariance (finiteIsingEnergy beta D)
      (fun eta u => spinSign (eta u)) (fun eta => spinSign (eta v))
      (fun u => (t : ℝ) * spinSign (p.1 u) + p.2 u) w ^ 2
  have hobs : Measurable (fun p : (TreeVertex d → IsingSpin) × (D → ℝ) =>
      fun u : D => (t : ℝ) * spinSign (p.1 u) + p.2 u) := by
    fun_prop
  have hbinary (eta : D → IsingSpin) : spinSign (eta v) = -1 ∨ spinSign (eta v) = 1 := by
    cases eta v <;> simp [spinSign]
  have hf : Measurable f :=
    (((FinitePosterior.continuous_normalizedFieldCovariance_entropy _ _ _ w hbinary
      ⟨fun _ => .neg, rfl⟩ ⟨fun _ => .pos, rfl⟩).measurable.comp hobs).pow_const 2)
  have hg : Measurable g :=
    (((FinitePosterior.continuous_fieldCovariance _ _ _ w).measurable.comp hobs).pow_const 2)
  simp_rw [shiftedRow_eq_normalized, shiftedRaw_eq_covariance] at hc
  have heF := hp.hasLaw.integral_comp hf.aestronglyMeasurable
  have heG := hp.hasLaw.integral_comp hg.aestronglyMeasurable
  change (∫ p, f (Prod.map id (fun ω (u : D) => B u t (ω u)) p)
    ∂μ.prod (Measure.infinitePi ν)) = _ at heF
  change (∫ p, g (Prod.map id (fun ω (u : D) => B u t (ω u)) p)
    ∂μ.prod (Measure.infinitePi ν)) = _ at heG
  have hobsEq (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) :
      finiteIsingBrownianObservation B D (t : ℝ) p =
        (fun u : D => (t : ℝ) * spinSign (p.1 u) + B u t (p.2 u)) := by
    funext u
    simp only [finiteIsingBrownianObservation, Real.toNNReal_coe]
  simp only [finiteIsingBrownianNormalizedCovariance, finiteIsingBrownianCovariance]
  simp_rw [hobsEq]
  simpa only [f, g, Prod.map_fst, Prod.map_snd, id_eq]
    using (show GaussianVarianceLower.varianceLower T (T + (d : ℝ) * beta) *
      (∫ p, f (Prod.map id (fun ω (u : D) => B u t (ω u)) p)
        ∂μ.prod (Measure.infinitePi ν)) ≤
      ∫ p, g (Prod.map id (fun ω (u : D) => B u t (ω u)) p)
        ∂μ.prod (Measure.infinitePi ν) by rw [heF, heG]; exact hc)

lemma integrable_coefficients_sq
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (ν : TreeVertex d → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hmB : ∀ i t, Measurable (B i t)) (beta : ℝ)
    (D : Finset (TreeVertex d)) (v w : D) (t : ℝ) :
    Integrable (fun p => finiteIsingBrownianNormalizedCovariance beta D v w B t p ^ 2)
      (μ.prod (Measure.infinitePi ν)) ∧
    Integrable (fun p => finiteIsingBrownianCovariance beta D v w B t p ^ 2)
      (μ.prod (Measure.infinitePi ν)) := by
  have hY : Measurable (finiteIsingBrownianObservation B D t) := by
    apply Measurable.of_eval
    intro u
    exact (((measurable_of_finite spinSign).comp
      ((measurable_pi_apply (u : TreeVertex d)).comp measurable_fst)).const_mul t).add
      ((hmB u t.toNNReal).comp ((measurable_pi_apply (u : TreeVertex d)).comp measurable_snd))
  have hs (eta : D → IsingSpin) (u : D) : spinSign (eta u) = -1 ∨ spinSign (eta u) = 1 := by
    cases eta u <;> simp [spinSign]
  have hb (eta : D → IsingSpin) (u : D) : |spinSign (eta u)| ≤ 1 := by
    cases eta u <;> norm_num [spinSign]
  constructor
  · apply Integrable.of_bound
      (((FinitePosterior.continuous_normalizedFieldCovariance_entropy (finiteIsingEnergy beta D)
        (fun eta u => spinSign (eta u)) (fun eta => spinSign (eta v)) w
        (fun eta => hs eta v) ⟨fun _ => .neg, rfl⟩ ⟨fun _ => .pos, rfl⟩).measurable.comp
        hY).pow_const 2).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_le_one_iff_abs_le_one]
      exact FinitePosterior.abs_normalizedFieldCovariance_le_one_entropy _ _ _ _ w
        (fun eta => hs eta v) ⟨fun _ => .neg, rfl⟩ ⟨fun _ => .pos, rfl⟩ (fun eta => hb eta w)
  · apply Integrable.of_bound
      (((FinitePosterior.continuous_fieldCovariance (finiteIsingEnergy beta D)
        (fun eta u => spinSign (eta u)) (fun eta => spinSign (eta v)) w).measurable.comp
        hY).pow_const 2).aestronglyMeasurable 4
    exact Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h := FinitePosterior.abs_fieldCovariance_le (finiteIsingEnergy beta D)
        (fun eta u => spinSign (eta u)) (fun eta => spinSign (eta v))
        (finiteIsingBrownianObservation B D t p) w 1 (fun eta => hs eta w) (fun eta => hb eta v)
      change finiteIsingBrownianCovariance beta D v w B t p ^ 2 ≤ 4
      have hsq := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).mpr
        (show |finiteIsingBrownianCovariance beta D v w B t p| ≤ 2 by simpa [finiteIsingBrownianCovariance] using h)
      norm_num only [sq_abs, Nat.reducePow, OfNat.ofNat] at hsq
      nlinarith [hsq]

theorem varianceLower_mul_integral_energy_le_information
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D)
    (hv : v.1.1 = []) {H T : ℝ} (hH : 0 ≤ H) (hT : 0 ≤ T) (hTH : T ≤ H) :
    GaussianVarianceLower.varianceLower H (H + (d : ℝ) * beta) *
      (∫ t in 0..T, ∫ p, ∑ w : D,
        finiteIsingBrownianNormalizedCovariance beta D v w B t p ^ 2
        ∂μ.prod (Measure.infinitePi ν)) ≤
      ∫ p, finiteIsingBrownianMean beta D v B T p ^ 2 ∂μ.prod (Measure.infinitePi ν) := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hn := hμ.integral_finiteIsingBrownianNormalizedEnergy_le hb ν hB hmB D hD v hT
  have hr := hμ.integral_finiteIsingBrownianEnergy ν hB hmB D hD v hT
  have hpoint (t : ℝ) (ht : t ∈ Icc 0 T) :
      GaussianVarianceLower.varianceLower H (H + (d : ℝ) * beta) *
        (∫ p, ∑ w : D, finiteIsingBrownianNormalizedCovariance beta D v w B t p ^ 2
          ∂μ.prod (Measure.infinitePi ν)) ≤
        ∫ p, ∑ w : D, finiteIsingBrownianCovariance beta D v w B t p ^ 2
          ∂μ.prod (Measure.infinitePi ν) := by
    rw [integral_finsetSum _ (fun w _ => (integrable_coefficients_sq μ ν hmB beta D v w t).1),
      integral_finsetSum _ (fun w _ => (integrable_coefficients_sq μ ν hmB beta D v w t).2),
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro w _
    have hh := varianceLower_mul_integral_normalized_sq_le_raw μ ν hb hB hmB
      D hD v w hv hH (t := t.toNNReal) (by simpa only [Real.coe_toNNReal t ht.1] using ht.2.trans hTH)
    simpa only [Real.coe_toNNReal t ht.1] using hh
  have hi := intervalIntegral.integral_mono_on hT
    (hn.1.const_mul (GaussianVarianceLower.varianceLower H (H + (d : ℝ) * beta))) hr.1 hpoint
  rw [intervalIntegral.integral_const_mul, hr.2.1] at hi
  exact hi

theorem lintegral_energy_le_information
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D)
    (hv : v.1.1 = []) {H T : ℝ} (hH : 0 ≤ H) (hT : 0 ≤ T) (hTH : T ≤ H) :
    (∫⁻ t in Ioc 0 T, ∫⁻ p,
      ENNReal.ofReal (∑ w : D, finiteIsingBrownianNormalizedCovariance beta D v w B t p ^ 2)
        ∂μ.prod (Measure.infinitePi ν)) ≤
      ENNReal.ofReal ((∫ p, finiteIsingBrownianMean beta D v B T p ^ 2
        ∂μ.prod (Measure.infinitePi ν)) /
          GaussianVarianceLower.varianceLower H (H + (d : ℝ) * beta)) := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let ρ := μ.prod (Measure.infinitePi ν)
  let R := fun t p => ∑ w : D, finiteIsingBrownianNormalizedCovariance beta D v w B t p ^ 2
  let E := fun t => ∫ p, R t p ∂ρ
  have hRpos (t : ℝ) (p) : 0 ≤ R t p := Finset.sum_nonneg fun w _ => sq_nonneg _
  have hRI (t : ℝ) : Integrable (R t) ρ :=
    integrable_finsetSum _ (fun w _ => (integrable_coefficients_sq μ ν hmB beta D v w t).1)
  have hinner (t : ℝ) : (∫⁻ p, ENNReal.ofReal (R t p) ∂ρ) = ENNReal.ofReal (E t) :=
    (ofReal_integral_eq_lintegral_ofReal (hRI t) (Filter.Eventually.of_forall (hRpos t))).symm
  have hn := hμ.integral_finiteIsingBrownianNormalizedEnergy_le hb ν hB hmB D hD v hT
  have hEI : Integrable E (volume.restrict (Ioc 0 T)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hn.1
  change (∫⁻ t in Ioc 0 T, ∫⁻ p, ENNReal.ofReal (R t p) ∂ρ) ≤ _
  simp_rw [hinner]
  rw [← ofReal_integral_eq_lintegral_ofReal hEI
    (Filter.Eventually.of_forall fun t => integral_nonneg (hRpos t)),
    ← intervalIntegral.integral_of_le hT]
  apply ENNReal.ofReal_le_ofReal
  apply (le_div_iff₀ (GaussianVarianceLower.varianceLower_pos _ _)).2
  simpa only [mul_comm] using
    varianceLower_mul_integral_energy_le_information hμ hb ν hB hmB D hD v hv hH hT hTH

end Problem367.NormalizedBrownianVarianceComparison

end

end OAI
