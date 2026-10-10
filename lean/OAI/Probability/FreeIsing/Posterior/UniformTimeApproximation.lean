import Mathlib.Topology.UniformSpace.Dini
import OAI.Probability.FreeIsing.Posterior.TimeL2Continuity

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367
open PlantedSymmetry

theorem HasFreeIsingLaw.finiteGibbsSpinMean_brownian_secondMoment_continuous
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i ω, Continuous (fun t => B i t ω)) (v : TreeVertex d) (n : ℕ) :
    Continuous (fun t : ℝ≥0 => ∫ p, finiteGibbsSpinMean beta v n
      (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  apply continuous_of_dominated (bound := fun _ => (1 : ℝ))
  · intro t
    apply Measurable.aestronglyMeasurable
    apply Measurable.pow_const
    apply (continuous_finiteGibbsSpinMean beta v n).measurable.comp
    apply Measurable.of_eval
    intro i
    exact (measurable_const.mul ((measurable_of_finite spinSign).comp
      ((measurable_pi_apply i).comp measurable_fst))).add
      ((hmB i t).comp ((measurable_pi_apply i).comp measurable_snd))
  · intro t
    exact Eventually.of_forall (fun p => by
      have h := pow_le_pow_left₀ (abs_nonneg _)
        (finiteGibbsSpinMean_abs_le_one beta v n
          (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i))) 2
      simpa only [Real.norm_eq_abs, abs_pow, sq_abs, one_pow] using h)
  · exact integrable_const _
  · exact Eventually.of_forall (fun p =>
      ((continuous_finiteGibbsSpinMean beta v n).comp
        (continuous_pi (fun i =>
          (continuous_subtype_val.mul continuous_const).add (hcB i (p.2 i))))).pow 2)

theorem HasFreeIsingLaw.finiteGibbsSpinMean_gaussian_secondMoment_monotone
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (t : ℝ≥0) (v : TreeVertex d) :
    Monotone (fun n => ∫ p, finiteGibbsSpinMean beta v n (observation t p) ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let ρ := μ.prod (gaussianNoiseLaw (TreeVertex d) t)
  let F := finiteObservationFiltration (connectedExhaustion v)
    (connectedExhaustion_monotone v) t
  let f := fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) => spinSign (p.1 v)
  let M := fun n => ρ[f | F n]
  have hmart : Martingale M F ρ := martingale_condExp f F ρ
  have hfbound : ∀ᵐ p ∂ρ, |f p| ≤ 1 :=
    Eventually.of_forall (fun p => by cases h : p.1 v <;> norm_num [f, spinSign, h])
  have h2 (n : ℕ) : MemLp (M n) 2 ρ := by
    apply MemLp.of_bound ((stronglyMeasurable_condExp.mono (F.le n)).aestronglyMeasurable) 1
    exact ae_bdd_abs_condExp_of_ae_bdd_abs hfbound
  have he (n : ℕ) : (∫ p, M n p ^ 2 ∂ρ) =
      ∫ p, finiteGibbsSpinMean beta v n (observation t p) ^ 2 ∂ρ := by
    apply integral_congr_ae
    exact (hμ.finiteObservation_condExp (connectedExhaustion v n)
      (connectedExhaustion_connected v n) t
      (fun eta => spinSign (eta ⟨v, mem_connectedExhaustion v n⟩))).fun_comp
        (fun x : ℝ => x ^ 2)
  intro n m hnm
  have heq := MartingaleTransformL2.integral_sq_increment_eq hmart hnm (h2 n) (h2 m)
  have hnonnegative : 0 ≤ ∫ p, (M m p - M n p) ^ 2 ∂ρ :=
    integral_nonneg (fun p => sq_nonneg _)
  rw [he m, he n] at heq
  change (∫ p, finiteGibbsSpinMean beta v n (observation t p) ^ 2 ∂ρ) ≤ _
  linarith

theorem HasFreeIsingLaw.finiteGibbsSpinMean_brownian_secondMoment_monotone
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v : TreeVertex d) :
    Monotone (fun n => ∫ p, finiteGibbsSpinMean beta v n
      (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have he (n : ℕ) := integral_brownian_ising_observation_eq_gaussian μ ν hB hmB t
    (fun y => finiteGibbsSpinMean beta v n y ^ 2)
    ((continuous_finiteGibbsSpinMean beta v n).measurable.pow_const 2)
  simpa only [he] using hμ.finiteGibbsSpinMean_gaussian_secondMoment_monotone t v

theorem HasFreeIsingLaw.finiteGibbsSpinMean_brownian_secondMoment_tendstoUniformlyOn
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i ω, Continuous (fun t => B i t ω)) (v : TreeVertex d)
    {K : Set ℝ≥0} (hK : IsCompact K) :
    TendstoUniformlyOn (fun n (t : ℝ≥0) => ∫ p, finiteGibbsSpinMean beta v n
      (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) ^ 2
      ∂μ.prod (Measure.infinitePi ν))
      (fun t => ∫ p, infiniteGibbsSpinMean beta v
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) ^ 2
        ∂μ.prod (Measure.infinitePi ν)) atTop K := by
  apply Monotone.tendstoUniformlyOn_of_forall_tendsto hK
  · intro n
    exact (hμ.finiteGibbsSpinMean_brownian_secondMoment_continuous ν hB hmB hcB v n).continuousOn
  · intro t ht
    exact hμ.finiteGibbsSpinMean_brownian_secondMoment_monotone ν hB hmB t v
  · exact (hμ.infiniteGibbsSpinMean_brownian_secondMoment_continuous hd hb hcrit
      ν hB hmB hcB v).continuousOn
  · intro t ht
    exact hμ.finiteGibbsSpinMean_brownian_tendsto_integral_sq ν hB hmB t v

private theorem integral_sq_sub_eq_sub_of_condExp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {X Y : Ω → ℝ}
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P) (hYm : StronglyMeasurable[m] Y)
    (hce : P[X | m] =ᵐ[P] Y) :
    (∫ ω, (X ω - Y ω) ^ 2 ∂P) =
      (∫ ω, X ω ^ 2 ∂P) - ∫ ω, Y ω ^ 2 ∂P := by
  have hD : MemLp (fun ω => X ω - Y ω) 2 P := hX.sub hY
  have hcross : Integrable (fun ω => Y ω * (X ω - Y ω)) P := hY.integrable_mul hD
  have hzero : P[X - Y | m] =ᵐ[P] 0 := by
    have he := condExp_sub (hX.integrable (by norm_num)) (hY.integrable (by norm_num)) m
    rw [condExp_of_stronglyMeasurable hm hYm (hY.integrable (by norm_num))] at he
    filter_upwards [he, hce] with ω hω hc
    simpa only [Pi.sub_apply, hc, sub_self, Pi.zero_apply] using hω
  have horth : (∫ ω, Y ω * (X ω - Y ω) ∂P) = 0 :=
    SimpleIntegral.integral_mul_eq_zero_of_condExp_eq_zero (mΩ := mΩ) (μ := P)
      (m := m) (H := Y) (D := fun ω => X ω - Y ω) hm hYm
      (hD.integrable (by norm_num)) hcross hzero
  have heq : (∫ ω, X ω ^ 2 ∂P) = (∫ ω, (X ω - Y ω) ^ 2 ∂P) +
      2 * (∫ ω, Y ω * (X ω - Y ω) ∂P) + ∫ ω, Y ω ^ 2 ∂P := by
    calc
      _ = ∫ ω, (X ω - Y ω) ^ 2 + 2 * (Y ω * (X ω - Y ω)) + Y ω ^ 2 ∂P := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun ω => by ring)
      _ = _ := by
        have h1 := integral_add hD.integrable_sq (hcross.const_mul 2)
        have h2 := integral_add (hD.integrable_sq.add (hcross.const_mul 2)) hY.integrable_sq
        simp only [Pi.add_apply] at h1 h2
        rw [h1, integral_const_mul] at h2
        exact h2
  rw [horth] at heq
  linarith

theorem HasFreeIsingLaw.finiteGibbsSpinMean_gaussian_meanSquare_eq_secondMoment_sub
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (t : ℝ≥0) (v : TreeVertex d) (n : ℕ) :
    (∫ p, (finiteGibbsSpinMean beta v n (observation t p) -
      infiniteGibbsSpinMean beta v (observation t p)) ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) =
      (∫ p, infiniteGibbsSpinMean beta v (observation t p) ^ 2
        ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) -
      ∫ p, finiteGibbsSpinMean beta v n (observation t p) ^ 2
        ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let m₀ : MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) := inferInstance
  let ρ := μ.prod (gaussianNoiseLaw (TreeVertex d) t)
  let F := finiteObservationFiltration (connectedExhaustion v)
    (connectedExhaustion_monotone v) t
  let m := observationSigma (TreeVertex d) t
  let f := fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) => spinSign (p.1 v)
  have hm : m ≤ m₀ := observationSigma_le (TreeVertex d) t
  have hFm : F n ≤ m := by
    change F n ≤ observationSigma (TreeVertex d) t
    rw [← finiteObservationFiltration_iSup (connectedExhaustion v)
      (connectedExhaustion_monotone v)
      (fun w => (eventually_mem_connectedExhaustion v w).exists) t]
    exact le_iSup (fun k => F k) n
  have hfbound : ∀ᵐ p ∂ρ, |f p| ≤ 1 :=
    Eventually.of_forall (fun p => by cases h : p.1 v <;> norm_num [f, spinSign, h])
  have h2 (m' : MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)))
      (hm' : m' ≤ m₀) : MemLp (ρ[f | m']) 2 ρ := by
    apply MemLp.of_bound ((stronglyMeasurable_condExp.mono hm').aestronglyMeasurable) 1
    exact ae_bdd_abs_condExp_of_ae_bdd_abs hfbound
  have he := integral_sq_sub_eq_sub_of_condExp (mΩ := m₀) (P := ρ) (m := F n) (F.le n) (h2 m hm) (h2 (F n) (F.le n))
    stronglyMeasurable_condExp (condExp_condExp_of_le hFm hm)
  have hfinite := hμ.finiteObservation_condExp (connectedExhaustion v n)
    (connectedExhaustion_connected v n) t
    (fun eta => spinSign (eta ⟨v, mem_connectedExhaustion v n⟩))
  have hinfinite := hμ.infiniteGibbsSpinMean_eq_posterior t v
  have hX : ρ[f | m] =ᵐ[ρ] fun p => infiniteGibbsSpinMean beta v (observation t p) :=
    hinfinite.symm
  have hY : ρ[f | F n] =ᵐ[ρ] fun p => finiteGibbsSpinMean beta v n (observation t p) :=
    hfinite
  have heL : (∫ p, ((ρ[f | m]) p - (ρ[f | F n]) p) ^ 2 ∂ρ) =
      ∫ p, (finiteGibbsSpinMean beta v n (observation t p) -
        infiniteGibbsSpinMean beta v (observation t p)) ^ 2 ∂ρ := by
    apply integral_congr_ae
    filter_upwards [hX, hY] with p hx hy
    rw [hx, hy]
    ring
  have heX : (∫ p, (ρ[f | m]) p ^ 2 ∂ρ) =
      ∫ p, infiniteGibbsSpinMean beta v (observation t p) ^ 2 ∂ρ :=
    integral_congr_ae (hX.fun_comp (fun x : ℝ => x ^ 2))
  have heY : (∫ p, (ρ[f | F n]) p ^ 2 ∂ρ) =
      ∫ p, finiteGibbsSpinMean beta v n (observation t p) ^ 2 ∂ρ :=
    integral_congr_ae (hY.fun_comp (fun x : ℝ => x ^ 2))
  rw [heL, heX, heY] at he
  exact he

theorem HasFreeIsingLaw.finiteGibbsSpinMean_brownian_meanSquare_eq_secondMoment_sub
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v : TreeVertex d) (n : ℕ) :
    (∫ p, (finiteGibbsSpinMean beta v n
      (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) -
      infiniteGibbsSpinMean beta v
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i))) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) =
      (∫ p, infiniteGibbsSpinMean beta v
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) ^ 2
        ∂μ.prod (Measure.infinitePi ν)) -
      ∫ p, finiteGibbsSpinMean beta v n
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) ^ 2
        ∂μ.prod (Measure.infinitePi ν) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hfin := (continuous_finiteGibbsSpinMean beta v n).measurable
  have hinf := measurable_infiniteGibbsSpinMean beta v
  rw [integral_brownian_ising_observation_eq_gaussian μ ν hB hmB t
      (fun y => (finiteGibbsSpinMean beta v n y - infiniteGibbsSpinMean beta v y) ^ 2)
      ((hfin.sub hinf).pow_const 2),
    integral_brownian_ising_observation_eq_gaussian μ ν hB hmB t
      (fun y => infiniteGibbsSpinMean beta v y ^ 2) (hinf.pow_const 2),
    integral_brownian_ising_observation_eq_gaussian μ ν hB hmB t
      (fun y => finiteGibbsSpinMean beta v n y ^ 2) (hfin.pow_const 2)]
  exact hμ.finiteGibbsSpinMean_gaussian_meanSquare_eq_secondMoment_sub t v n

theorem HasFreeIsingLaw.finiteGibbsSpinMean_brownian_meanSquare_tendstoUniformlyOn
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i ω, Continuous (fun t => B i t ω)) (v : TreeVertex d)
    {K : Set ℝ≥0} (hK : IsCompact K) :
    TendstoUniformlyOn (fun n (t : ℝ≥0) => ∫ p,
      (finiteGibbsSpinMean beta v n
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) -
      infiniteGibbsSpinMean beta v
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i))) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) (fun _ => 0) atTop K := by
  have he := hμ.finiteGibbsSpinMean_brownian_secondMoment_tendstoUniformlyOn
    hd hb hcrit ν hB hmB hcB v hK
  rw [Metric.tendstoUniformlyOn_iff] at he ⊢
  intro ε hε
  filter_upwards [he ε hε] with n hn t ht
  rw [hμ.finiteGibbsSpinMean_brownian_meanSquare_eq_secondMoment_sub ν hB hmB t v n]
  simpa only [Real.dist_eq, sub_zero, zero_sub, abs_neg, abs_sub_comm] using hn t ht

end Problem367

end

end OAI
