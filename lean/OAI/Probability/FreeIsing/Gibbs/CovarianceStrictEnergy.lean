import OAI.Probability.FreeIsing.Energy.FiniteIsingEnergyLimit
import OAI.Probability.FreeIsing.Gibbs.CovarianceStrictConvergence

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology BigOperators
namespace Problem367

local instance covarianceStrictEnergyNonemptyIsingSpin : Nonempty IsingSpin := ⟨.neg⟩

lemma finiteGibbsSpinMean_abs_le_one {d : ℕ} (beta : ℝ)
    (v : TreeVertex d) (n : ℕ) (y : TreeVertex d → ℝ) :
    |finiteGibbsSpinMean beta v n y| ≤ 1 := by
  apply FinitePosterior.abs_fieldMean_le
  intro eta
  cases eta ⟨v, mem_connectedExhaustion v n⟩ <;> norm_num [spinSign]

lemma finiteGibbsCovariance_self {d : ℕ} (beta : ℝ)
    (v : TreeVertex d) (n : ℕ) (y : TreeVertex d → ℝ) :
    finiteGibbsCovariance beta v v n y = 1 - finiteGibbsSpinMean beta v n y ^ 2 := by
  classical
  simp only [finiteGibbsCovariance, dite_eq_left (mem_connectedExhaustion v n)]
  unfold finiteGibbsCovarianceOn finiteGibbsSpinMean
  have heq : (fun eta : connectedExhaustion v n → IsingSpin =>
      spinSign (eta ⟨v, mem_connectedExhaustion v n⟩) *
        spinSign (eta ⟨v, mem_connectedExhaustion v n⟩)) = fun _ => (1 : ℝ) := by
    funext eta
    cases eta ⟨v, mem_connectedExhaustion v n⟩ <;> norm_num [spinSign]
  rw [heq, FinitePosterior.fieldMean_const, pow_two]

theorem HasFreeIsingLaw.finiteGibbsSpinMean_brownian_tendsto_integral_sq
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v : TreeVertex d) :
    Tendsto (fun n => ∫ p,
      finiteGibbsSpinMean beta v n
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) atTop
      (𝓝 (∫ p, infiniteGibbsSpinMean beta v
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) ^ 2
        ∂μ.prod (Measure.infinitePi ν))) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let X := fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
    fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)
  have hX : Measurable X := by
    apply Measurable.of_eval
    intro i
    exact (measurable_const.mul ((measurable_of_finite spinSign).comp
      ((measurable_pi_apply i).comp measurable_fst))).add
      ((hmB i t).comp ((measurable_pi_apply i).comp measurable_snd))
  apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun n => (((continuous_finiteGibbsSpinMean beta v n).measurable.comp hX).pow_const 2).aestronglyMeasurable)
    (integrable_const 1)
  · intro n
    filter_upwards with p
    have hs := pow_le_pow_left₀ (abs_nonneg _)
      (finiteGibbsSpinMean_abs_le_one beta v n (X p)) 2
    simpa only [Function.comp_def, Real.norm_eq_abs, abs_pow, sq_abs, one_pow] using hs
  · filter_upwards [hμ.finiteGibbsCovariance_brownian_tendsto_ae ν hB hmB t v v]
      with p hp
    simpa only [finiteGibbsCovariance_self, infiniteGibbsCovariance_self,
      sub_sub_cancel, Function.comp_def, X] using hp.const_sub 1

theorem HasFreeIsingLaw.finiteGibbsCovariance_timeEnergy_eq
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (v : TreeVertex d) (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∑' w, ∫ p, finiteGibbsCovariance beta v w n (brownianIsingObservationR B p) ^ 2
      ∂(volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν))) =
    ∫ p, finiteGibbsSpinMean beta v n (brownianIsingObservationR B (T, p)) ^ 2
      ∂μ.prod (Measure.infinitePi ν) := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let D := connectedExhaustion v n
  let ρ := μ.prod (Measure.infinitePi ν)
  let τ : Measure ℝ := volume.restrict (Ioc 0 T)
  let C := fun w p => finiteGibbsCovariance beta v w n (brownianIsingObservationR B p)
  have hi (w : TreeVertex d) : Integrable (fun p => C w p ^ 2) (τ.prod ρ) :=
    integrable_finiteGibbsCovariance_sq beta v w n (measurable_brownianIsingObservationR hmB hcB)
  have hsum : Integrable (fun p => ∑ w ∈ D, C w p ^ 2) (τ.prod ρ) :=
    integrable_finsetSum D (fun w _ => hi w)
  have heq (p : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω))) :
      (∑ w ∈ D, C w p ^ 2) =
      ∑ w : D, finiteIsingBrownianCovariance beta D
        ⟨v, mem_connectedExhaustion v n⟩ w B p.1 p.2 ^ 2 := by
    rw [← Finset.sum_attach D]
    apply Finset.sum_congr rfl
    intro w _
    rw [show C w p = finiteIsingBrownianCovariance beta D
      ⟨v, mem_connectedExhaustion v n⟩ w B p.1 p.2 from
        finiteGibbsCovariance_eq_finiteIsingBrownianCovariance beta v n B p w]
  have he := hμ.integral_finiteIsingBrownianEnergy ν hB hmB D
    (connectedExhaustion_connected v n) ⟨v, mem_connectedExhaustion v n⟩ hT
  calc
    (∑' w, ∫ p, C w p ^ 2 ∂τ.prod ρ) = ∑ w ∈ D, ∫ p, C w p ^ 2 ∂τ.prod ρ := by
      apply tsum_eq_sum
      intro w hw
      change w ∉ connectedExhaustion v n at hw
      simp only [C, finiteGibbsCovariance, dite_eq_right hw, zero_pow (by decide : 2 ≠ 0), integral_zero]
    _ = ∫ p, ∑ w ∈ D, C w p ^ 2 ∂τ.prod ρ :=
      (integral_finsetSum D (fun w _ => hi w)).symm
    _ = ∫ t, ∫ p, ∑ w ∈ D, C w (t, p) ^ 2 ∂ρ ∂τ := integral_prod _ hsum
    _ = ∫ t in (0 : ℝ)..T, ∫ p, ∑ w : D,
        finiteIsingBrownianCovariance beta D ⟨v, mem_connectedExhaustion v n⟩ w B t p ^ 2 ∂ρ := by
      rw [intervalIntegral.integral_of_le hT]
      apply integral_congr_ae
      filter_upwards with t
      apply integral_congr_ae
      filter_upwards with p
      exact heq (t, p)
    _ = ∫ p, finiteIsingBrownianMean beta D ⟨v, mem_connectedExhaustion v n⟩ B T p ^ 2 ∂ρ := he.2.1
    _ = _ := rfl

theorem HasFreeIsingLaw.infiniteGibbsCovariance_timeEnergy_eq_of_strict
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (v : TreeVertex d) {T : ℝ} (hT : 0 ≤ T) :
    let P := (volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν))
    let C := fun w p => infiniteGibbsCovariance beta v w (brownianIsingObservationR B p)
    let M := ∫ p, infiniteGibbsSpinMean beta v (brownianIsingObservationR B (T, p)) ^ 2
      ∂μ.prod (Measure.infinitePi ν)
    HasSum (fun w => ∫ p, C w p ^ 2 ∂P) M ∧
      (∫ p, ∑' w, C w p ^ 2 ∂P) = M := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let P := (volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν))
  let C := fun w p => infiniteGibbsCovariance beta v w (brownianIsingObservationR B p)
  let Cn := fun n w p => finiteGibbsCovariance beta v w n (brownianIsingObservationR B p)
  let M := ∫ p, infiniteGibbsSpinMean beta v (brownianIsingObservationR B (T, p)) ^ 2
    ∂μ.prod (Measure.infinitePi ν)
  have hX := measurable_brownianIsingObservationR hmB hcB
  have hi (n : ℕ) (w : TreeVertex d) : Integrable (fun p => Cn n w p ^ 2) P :=
    integrable_finiteGibbsCovariance_sq beta v w n hX
  have hbound (n : ℕ) (w : TreeVertex d) :
      (∫ p, Cn n w p ^ 2 ∂P) ≤
        P.real univ * (Real.tanh beta ^ 2) ^ reducedWordDistance v.1 w.1 := by
    calc
      _ ≤ ∫ _p, (Real.tanh beta ^ reducedWordDistance v.1 w.1) ^ 2 ∂P := by
        apply integral_mono (hi n w) (integrable_const _)
        intro p
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
          (finiteGibbsCovariance_abs_le_distance hb v w n (brownianIsingObservationR B p)) 2
      _ = _ := by
        rw [integral_const, smul_eq_mul]
        congr 1
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hs := (summable_geometric_intrinsic v (sq_nonneg (Real.tanh beta)) hstrict).mul_left
    (P.real univ)
  have hlim : Tendsto (fun n => ∑' w, ∫ p, Cn n w p ^ 2 ∂P) atTop
      (𝓝 (∑' w, ∫ p, C w p ^ 2 ∂P)) := by
    apply tendsto_tsum_of_dominated_convergence hs
      (fun w => hμ.finiteGibbsCovariance_tendsto_timeSquareIntegral ν hB hmB hcB v w)
    exact Eventually.of_forall fun n w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun p => sq_nonneg _))]
      exact hbound n w
  have hterminal : Tendsto (fun n => ∫ p,
      finiteGibbsSpinMean beta v n (brownianIsingObservationR B (T, p)) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) atTop (𝓝 M) := by
    have h := hμ.finiteGibbsSpinMean_brownian_tendsto_integral_sq ν hB hmB T.toNNReal v
    rw [Real.coe_toNNReal T hT] at h
    convert h using 1 <;> rfl
  have hfinite (n : ℕ) : (∑' w, ∫ p, Cn n w p ^ 2 ∂P) =
      ∫ p, finiteGibbsSpinMean beta v n (brownianIsingObservationR B (T, p)) ^ 2
        ∂μ.prod (Measure.infinitePi ν) :=
    hμ.finiteGibbsCovariance_timeEnergy_eq ν hB hmB hcB v n hT
  have heq : (∑' w, ∫ p, C w p ^ 2 ∂P) = M :=
    tendsto_nhds_unique hlim (hterminal.congr' (Eventually.of_forall fun n => (hfinite n).symm))
  have hrow := hμ.infiniteGibbsCovariance_timeEnergy ν hB hmB hcB v hT
  have hh : HasSum (fun w => ∫ p, C w p ^ 2 ∂P) M := by
    rw [← heq]
    exact hrow.1.hasSum
  have hident := DiscrepancyEnergy.hasSum_integral_sq_row
    (fun w => ((measurable_infiniteGibbsCovariance beta v w).comp hX).aestronglyMeasurable)
    hrow.2.2.1 hrow.2.2.2.1
  dsimp only
  exact ⟨hh, hident.unique hh⟩

end Problem367

end

end OAI
