import OAI.Probability.FreeIsing.Conditioning.FiniteEntropySmallTime
import OAI.Probability.FreeIsing.Stochastic.NormalizedBrownianVarianceComparison

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace Problem367.NormalizedCriticalInitialEnergy

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

def informationConstant (beta : ℝ) : ℝ :=
  (1 + Real.tanh beta ^ 2) *
    Real.sqrt (1 / ((1 - Real.tanh beta ^ 2) * Real.tanh beta ^ 4))

lemma informationConstant_nonneg (beta : ℝ) : 0 ≤ informationConstant beta := by
  unfold informationConstant
  positivity

def energyConstant (d : ℕ) (beta : ℝ) : ℝ :=
  informationConstant beta / GaussianVarianceLower.varianceLower 1 (1 + (d : ℝ) * beta)

lemma energyConstant_nonneg (d : ℕ) (beta : ℝ) : 0 ≤ energyConstant d beta :=
  div_nonneg (informationConstant_nonneg beta) (GaussianVarianceLower.varianceLower_pos _ _).le

theorem lintegral_finite_energy_le
    (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D)
    (hv : v.1.1 = []) (T : ℝ≥0) (hT : (T : ℝ) ≤ 1) :
    (∫⁻ t in Ioc 0 (T : ℝ), ∫⁻ p,
      ENNReal.ofReal (∑ w : D, finiteIsingBrownianNormalizedCovariance beta D v w B t p ^ 2)
        ∂μ.prod (Measure.infinitePi ν)) ≤
      ENNReal.ofReal (energyConstant d beta * Real.sqrt (T : ℝ)) := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have h := NormalizedBrownianVarianceComparison.lintegral_energy_le_information
    hμ hb ν hB hmB D hD v hv (by norm_num : (0 : ℝ) ≤ 1) T.property hT
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hm := div_le_div_of_nonneg_right
    (hμ.finiteIsingBrownian_critical_information_upper hd hb hcrit ν hB hmB D hD v T hT)
    (GaussianVarianceLower.varianceLower_pos 1 (1 + (d : ℝ) * beta)).le
  change _ ≤ informationConstant beta / GaussianVarianceLower.varianceLower 1
    (1 + (d : ℝ) * beta) * Real.sqrt (T : ℝ)
  convert hm using 1 <;> first | rfl | (dsimp [informationConstant]; ring)

theorem lintegral_infinite_energy_le
    (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hjoint : ∀ i, Measurable (fun z : ℝ≥0 × Ω => B i z.1 z.2))
    (v : TreeVertex d) (hv : v.1 = []) (T : ℝ≥0) (hT : (T : ℝ) ≤ 1) :
    (∫⁻ q, ∑' w, ENNReal.ofReal
      (NormalizedInfiniteTimeEnergy.infiniteRow beta v B w q ^ 2)
      ∂(volume.restrict (Ioc 0 (T : ℝ))).prod (μ.prod (Measure.infinitePi ν))) ≤
      ENNReal.ofReal (energyConstant d beta * Real.sqrt (T : ℝ)) := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  apply NormalizedInfiniteTimeEnergy.lintegral_infiniteRow_le_of_finite hμ hb ν hB hmB hjoint
    (connectedExhaustion v) (connectedExhaustion_monotone v)
    (connectedExhaustion_connected v)
    (fun u => (eventually_mem_connectedExhaustion v u).exists)
    v (mem_connectedExhaustion v) T
  intro n
  let D := connectedExhaustion v n
  let r : D := ⟨v, mem_connectedExhaustion v n⟩
  let R : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) → ℝ≥0∞ :=
    fun q => ENNReal.ofReal (∑ w : D,
      finiteIsingBrownianNormalizedCovariance beta D r w B q.1 q.2 ^ 2)
  have hR : Measurable R := by
    have heq : R = fun q => ∑' w, ENNReal.ofReal
        (NormalizedInfiniteTimeEnergy.finiteRow beta D v B w q ^ 2) := by
      funext q
      exact (NormalizedInfiniteTimeEnergy.tsum_finiteRow_sq beta D r B q).symm
    rw [heq]
    exact Measurable.tsum (fun w =>
      ((NormalizedInfiniteTimeEnergy.measurable_finiteRow beta D v hjoint w).pow_const 2).ennreal_ofReal)
  calc
    _ = ∫⁻ q, R q
        ∂(volume.restrict (Ioc 0 (T : ℝ))).prod (μ.prod (Measure.infinitePi ν)) := by
      apply lintegral_congr
      intro q
      exact (ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)).symm
    _ = ∫⁻ t in Ioc 0 (T : ℝ), ∫⁻ p, R (t, p) ∂μ.prod (Measure.infinitePi ν) :=
      lintegral_prod R hR.aemeasurable
    _ ≤ _ := lintegral_finite_energy_le hd hμ hb hcrit ν hB hmB
      D (connectedExhaustion_connected v n) r hv T hT

theorem tendsto_infinite_energy_zero
    (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hjoint : ∀ i, Measurable (fun z : ℝ≥0 × Ω => B i z.1 z.2))
    (v : TreeVertex d) (hv : v.1 = []) :
    Tendsto (fun T : ℝ≥0 => ∫⁻ q, ∑' w, ENNReal.ofReal
      (NormalizedInfiniteTimeEnergy.infiniteRow beta v B w q ^ 2)
      ∂(volume.restrict (Ioc 0 (T : ℝ))).prod (μ.prod (Measure.infinitePi ν)))
      (𝓝 0) (𝓝 0) := by
  have hc : Continuous (fun T : ℝ≥0 =>
      ENNReal.ofReal (energyConstant d beta * Real.sqrt (T : ℝ))) :=
    ENNReal.continuous_ofReal.comp
      (continuous_const.mul (Real.continuous_sqrt.comp NNReal.continuous_coe))
  have hlim : Tendsto (fun T : ℝ≥0 =>
      ENNReal.ofReal (energyConstant d beta * Real.sqrt (T : ℝ))) (𝓝 0) (𝓝 0) := by
    simpa only [NNReal.coe_zero, Real.sqrt_zero, mul_zero, ENNReal.ofReal_zero] using hc.tendsto 0
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [eventually_lt_nhds (by norm_num : (0 : ℝ≥0) < 1)] with T hT
  exact lintegral_infinite_energy_le hd hμ hb hcrit ν hB hmB hjoint v hv T
    (by exact_mod_cast hT.le)

end Problem367.NormalizedCriticalInitialEnergy

end

end OAI
