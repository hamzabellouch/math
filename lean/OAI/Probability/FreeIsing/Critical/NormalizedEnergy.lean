import OAI.Probability.FreeIsing.Conditioning.FiniteEntropySmallTime
import OAI.Probability.FreeIsing.Energy.NormalizedInfiniteTimeEnergy

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Problem367

local instance : Nonempty IsingSpin := ⟨.neg⟩

theorem HasFreeIsingLaw.lintegral_finiteIsingBrownianNormalizedEnergy_le_entropy
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫⁻ t in Ioc 0 T, ∫⁻ p,
      ENNReal.ofReal (∑ u : D, finiteIsingBrownianNormalizedCovariance beta D v u B t p ^ 2)
      ∂μ.prod (Measure.infinitePi ν)) ≤
      ENNReal.ofReal (∫ p, finiteIsingBrownianEntropy beta D v B T p
        ∂μ.prod (Measure.infinitePi ν)) := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let ρ := μ.prod (Measure.infinitePi ν)
  let R := fun t p => ∑ u : D, finiteIsingBrownianNormalizedCovariance beta D v u B t p ^ 2
  let E : ℝ → ℝ := fun t => ∫ p, R t p ∂ρ
  have hRpos (t : ℝ) (p) : 0 ≤ R t p := Finset.sum_nonneg fun u _ => sq_nonneg _
  have hRI (t : ℝ) : Integrable (R t) ρ := by
    have hY : Measurable (finiteIsingBrownianObservation B D t) := by
      apply Measurable.of_eval
      intro w
      exact (((measurable_of_finite spinSign).comp
        ((measurable_pi_apply (w : TreeVertex d)).comp measurable_fst)).const_mul t).add
        ((hmB w t.toNNReal).comp ((measurable_pi_apply (w : TreeVertex d)).comp measurable_snd))
    have hs (eta : D → IsingSpin) : spinSign (eta v) = -1 ∨ spinSign (eta v) = 1 := by
      cases eta v <;> simp [spinSign]
    have hn : ∃ eta : D → IsingSpin, spinSign (eta v) = -1 := ⟨fun _ => .neg, rfl⟩
    have hp : ∃ eta : D → IsingSpin, spinSign (eta v) = 1 := ⟨fun _ => .pos, rfl⟩
    apply Integrable.of_bound
      ((FinitePosterior.continuous_normalizedRowEnergy (finiteIsingEnergy beta D)
        (fun (eta : D → IsingSpin) w => spinSign (eta w)) (fun eta => spinSign (eta v))
        hs hn hp).measurable.comp hY).aestronglyMeasurable (Fintype.card D)
    exact Eventually.of_forall fun p => by
      simpa only [Real.norm_eq_abs, Function.comp_def] using
        FinitePosterior.abs_normalizedRowEnergy_le_card (finiteIsingEnergy beta D)
          (fun (eta : D → IsingSpin) w => spinSign (eta w)) (fun eta => spinSign (eta v))
          (finiteIsingBrownianObservation B D t p) hs hn hp
          (fun eta w => by cases eta w <;> norm_num [spinSign])
  have hinner (t : ℝ) : (∫⁻ p, ENNReal.ofReal (R t p) ∂ρ) = ENNReal.ofReal (E t) :=
    (ofReal_integral_eq_lintegral_ofReal (hRI t) (Eventually.of_forall (hRpos t))).symm
  have hbound := hμ.integral_finiteIsingBrownianNormalizedEnergy_le hbeta ν hB hmB D hD v hT
  have hEI : Integrable E (volume.restrict (Ioc 0 T)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hbound.1
  change (∫⁻ t in Ioc 0 T, ∫⁻ p, ENNReal.ofReal (R t p) ∂ρ) ≤ _
  simp_rw [hinner]
  rw [← ofReal_integral_eq_lintegral_ofReal hEI
    (Eventually.of_forall fun t => integral_nonneg (hRpos t))]
  rw [← intervalIntegral.integral_of_le hT]
  exact ENNReal.ofReal_le_ofReal hbound.2.1

namespace NormalizedInfiniteTimeEnergy

theorem lintegral_infiniteRow_le_criticalEnvelope
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 = 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hjoint : ∀ i, Measurable (fun z : ℝ≥0 × Ω => B i z.1 z.2))
    (v : TreeVertex d) (T : ℝ≥0) (hT : (T : ℝ) ≤ 1) :
    (∫⁻ q, ∑' w, ENNReal.ofReal (infiniteRow beta v B w q ^ 2)
      ∂(volume.restrict (Ioc 0 (T : ℝ))).prod (μ.prod (Measure.infinitePi ν))) ≤
      ENNReal.ofReal (criticalEntropyEnvelope d beta T) := by
  let := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  apply lintegral_infiniteRow_le_of_finite hμ hb ν hB hmB hjoint
    (connectedExhaustion v) (connectedExhaustion_monotone v)
    (connectedExhaustion_connected v)
    (fun u => (eventually_mem_connectedExhaustion v u).exists)
    v (mem_connectedExhaustion v) T
  intro n
  let D := connectedExhaustion v n
  let r : D := ⟨v, mem_connectedExhaustion v n⟩
  let R : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) → ℝ≥0∞ :=
    fun q => ENNReal.ofReal (∑ u : D,
      finiteIsingBrownianNormalizedCovariance beta D r u B q.1 q.2 ^ 2)
  have hR : Measurable R := by
    have heq : R = fun q => ∑' w, ENNReal.ofReal (finiteRow beta D v B w q ^ 2) := by
      funext q
      exact (tsum_finiteRow_sq beta D r B q).symm
    rw [heq]
    exact Measurable.tsum (fun w =>
      ((measurable_finiteRow beta D v hjoint w).pow_const 2).ennreal_ofReal)
  calc
    _ = ∫⁻ q, R q
        ∂(volume.restrict (Ioc 0 (T : ℝ))).prod (μ.prod (Measure.infinitePi ν)) := by
      apply lintegral_congr
      intro q
      exact (ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)).symm
    _ = ∫⁻ t in Ioc 0 (T : ℝ), ∫⁻ p, R (t, p) ∂μ.prod (Measure.infinitePi ν) :=
      lintegral_prod R hR.aemeasurable
    _ ≤ ENNReal.ofReal (∫ p, finiteIsingBrownianEntropy beta D r B T p
        ∂μ.prod (Measure.infinitePi ν)) :=
      hμ.lintegral_finiteIsingBrownianNormalizedEnergy_le_entropy hb ν hB hmB
        D (connectedExhaustion_connected v n) r T.property
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (hμ.finiteIsingBrownianEntropy_le_criticalEnvelope hd hb hcritical ν hB hmB
        D (connectedExhaustion_connected v n) r T hT)

theorem tendsto_lintegral_infiniteRow_critical_zero
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 = 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hjoint : ∀ i, Measurable (fun z : ℝ≥0 × Ω => B i z.1 z.2))
    (v : TreeVertex d) :
    Tendsto (fun T : ℝ≥0 =>
      ∫⁻ q, ∑' w, ENNReal.ofReal (infiniteRow beta v B w q ^ 2)
        ∂(volume.restrict (Ioc 0 (T : ℝ))).prod (μ.prod (Measure.infinitePi ν)))
      (𝓝 0) (𝓝 0) := by
  have hc : Continuous (fun T : ℝ≥0 =>
      ENNReal.ofReal (criticalEntropyEnvelope d beta T)) :=
    ENNReal.continuous_ofReal.comp ((continuous_criticalEntropyEnvelope d beta).comp
      NNReal.continuous_coe)
  have hlim : Tendsto (fun T : ℝ≥0 => ENNReal.ofReal (criticalEntropyEnvelope d beta T))
      (𝓝 0) (𝓝 0) := by simpa using hc.tendsto 0
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · exact Eventually.of_forall fun _ => zero_le
  · filter_upwards [eventually_lt_nhds (by norm_num : (0 : ℝ≥0) < 1)] with T hT
    exact lintegral_infiniteRow_le_criticalEnvelope hd hμ hb hcritical ν hB hmB hjoint
      v T (by exact_mod_cast hT.le)

end NormalizedInfiniteTimeEnergy
end Problem367

end

end OAI
