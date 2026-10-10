import OAI.Probability.FreeIsing.Brownian.ArrayObservation
import OAI.Probability.FreeIsing.Stochastic.SimpleIntegralIsometry

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem planted_coordinate_preBrownian
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i)) (i : ι) :
    IsPreBrownianReal (fun t (q : S × (ι → Ω)) => B i t (q.2 i))
      (ν.prod (Measure.infinitePi μ)) where
  hasLaw I := by
    have (j : ι) : IsProbabilityMeasure (μ j) :=
      (hB j).isGaussianProcess.isProbabilityMeasure
    exact ((hB i).hasLaw I).comp
      (planted_noise_coordinate_measurePreserving ν μ i).hasLaw

theorem planted_coordinate_increments_indep
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t)) (s t : ℝ≥0) {i j : ι} (hij : i ≠ j) :
    IndepFun (fun q : S × (ι → Ω) => B i t (q.2 i) - B i s (q.2 i))
      (fun q : S × (ι → Ω) => B j t (q.2 j) - B j s (q.2 j))
      (ν.prod (Measure.infinitePi μ)) := by
  have (k : ι) : IsProbabilityMeasure (μ k) :=
    (hB k).isGaussianProcess.isProbabilityMeasure
  have hind := (iIndepFun_infinitePi
    (fun k => (hmB k t).sub (hmB k s)) (P := μ)).indepFun hij
  exact indepFun_comp_measurePreserving measurePreserving_snd
    (((hmB i t).sub (hmB i s)).comp (measurable_pi_apply i))
    (((hmB j t).sub (hmB j s)).comp (measurable_pi_apply j)) hind

theorem planted_weighted_increment_integral_sq
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t)) {s t : ℝ≥0} (hst : s ≤ t)
    (I : Finset ι) (a : ι → ℝ) :
    (∫ q : S × (ι → Ω),
      (∑ i ∈ I, a i * (B i t (q.2 i) - B i s (q.2 i))) ^ 2
        ∂ν.prod (Measure.infinitePi μ)) =
      ((t : ℝ) - (s : ℝ)) * ∑ i ∈ I, a i ^ 2 := by
  classical
  have (k : ι) : IsProbabilityMeasure (μ k) :=
    (hB k).isGaussianProcess.isProbabilityMeasure
  let P := ν.prod (Measure.infinitePi μ)
  let D : ι → S × (ι → Ω) → ℝ := fun i q => B i t (q.2 i) - B i s (q.2 i)
  have hC (i : ι) := planted_coordinate_preBrownian ν μ hB i
  have hD2 (i : ι) : MemLp (D i) 2 P :=
    ((hC i).isGaussianProcess.hasGaussianLaw_eval t).memLp_two.sub
      ((hC i).isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  have hY2 (i : ι) : MemLp (fun q => a i * D i q) 2 P := (hD2 i).const_mul (a i)
  have hzero (i : ι) : (∫ q, D i q ∂P) = 0 := by
    change (∫ q : S × (ι → Ω), B i t (q.2 i) - B i s (q.2 i) ∂P) = 0
    rw [integral_sub ((hC i).integrable_eval t) ((hC i).integrable_eval s),
      (hC i).integral_eval, (hC i).integral_eval, sub_self]
  have hsq (i : ι) : (∫ q, D i q ^ 2 ∂P) = (t : ℝ) - (s : ℝ) := by
    have h := preBrownian_integral_sq ((hC i).shift s) (t - s)
    simpa only [D, add_tsub_cancel_of_le hst, NNReal.coe_sub hst] using h
  have horth (i : ι) (_hi : i ∈ I) (j : ι) (_hj : j ∈ I) (hij : i ≠ j) :
      (∫ q, (a i * D i q) * (a j * D j q) ∂P) = 0 := by
    have hind := (planted_coordinate_increments_indep ν μ hB hmB s t hij).comp
      (measurable_id.const_mul (a i)) (measurable_id.const_mul (a j))
    have heq := hind.integral_mul_eq_mul_integral
      (hY2 i).aestronglyMeasurable (hY2 j).aestronglyMeasurable
    change (∫ q, (a i * D i q) * (a j * D j q) ∂P) =
      (∫ q, a i * D i q ∂P) * (∫ q, a j * D j q ∂P) at heq
    simpa only [integral_const_mul, hzero, mul_zero, zero_mul] using heq
  rw [SimpleIntegral.integral_sq_sum_of_orthogonal I (fun i q => a i * D i q)
    (fun i _ j _ => (hY2 i).integrable_mul (hY2 j)) horth]
  simp only [mul_pow, integral_const_mul, hsq]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem planted_weighted_increment_sq_condExp
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t)) {s t : ℝ≥0} (hst : s ≤ t)
    (I : Finset ι) (a : ι → ℝ) :
    (ν.prod (Measure.infinitePi μ))[
      (fun q : S × (ι → Ω) =>
        (∑ i ∈ I, a i * (B i t (q.2 i) - B i s (q.2 i))) ^ 2) |
      signalArrayFiltration B hmB s] =ᵐ[ν.prod (Measure.infinitePi μ)]
        fun _ => ((t : ℝ) - (s : ℝ)) * ∑ i ∈ I, a i ^ 2 := by
  classical
  have (k : ι) : IsProbabilityMeasure (μ k) :=
    (hB k).isGaussianProcess.isProbabilityMeasure
  have hm : Measurable (fun x : ι → ℝ => (∑ i ∈ I, a i * x i) ^ 2) := by
    fun_prop
  have hind := (planted_array_increments_indep_signal_past ν μ hB hmB hst).comp
    hm measurable_id
  have hf : Measurable (fun q : S × (ι → Ω) =>
      (∑ i ∈ I, a i * (B i t (q.2 i) - B i s (q.2 i))) ^ 2) := by
    apply hm.comp
    exact Measurable.of_eval fun i =>
      ((hmB i t).sub (hmB i s)).comp ((measurable_pi_apply i).comp measurable_snd)
  have hn := signalArrayFiltration_eq_comap (S := S) B hmB s
  have hc := condExp_indep_eq hf.comap_le
    (hn ▸ (signalArrayFiltration (S := S) B hmB).le s)
    (measurable_iff_comap_le.mpr le_rfl).stronglyMeasurable hind
  simp only [Function.id_comp] at hc
  rw [← hn] at hc
  simpa only [Function.comp_def, id_eq,
    planted_weighted_increment_integral_sq ν μ hB hmB hst I a] using hc

theorem planted_weighted_increment_sq_condExp_subfield
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t)) {s t : ℝ≥0} (hst : s ≤ t)
    (I : Finset ι) (a : ι → ℝ)
    {m : MeasurableSpace (S × (ι → Ω))} (hm : m ≤ signalArrayFiltration B hmB s) :
    (ν.prod (Measure.infinitePi μ))[
      (fun q : S × (ι → Ω) =>
        (∑ i ∈ I, a i * (B i t (q.2 i) - B i s (q.2 i))) ^ 2) | m]
      =ᵐ[ν.prod (Measure.infinitePi μ)]
        fun _ => ((t : ℝ) - (s : ℝ)) * ∑ i ∈ I, a i ^ 2 := by
  have (k : ι) : IsProbabilityMeasure (μ k) :=
    (hB k).isGaussianProcess.isProbabilityMeasure
  exact ((condExp_condExp_of_le hm (signalArrayFiltration (S := S) B hmB |>.le s)).symm.trans
    (condExp_congr_ae (planted_weighted_increment_sq_condExp ν μ hB hmB hst I a))).trans
      (Filter.EventuallyEq.of_eq (condExp_const (hm.trans
        (signalArrayFiltration (S := S) B hmB |>.le s)) _))

end Problem367

end

end OAI
