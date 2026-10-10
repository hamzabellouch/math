import OAI.Probability.FreeIsing.Brownian.Martingale
import OAI.Probability.FreeIsing.Stochastic.SimpleIntegralIsometry

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem preBrownian_increment_indep_of_past_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t)) {s t : ℝ≥0} (hst : s ≤ t)
    {H : Ω → ℝ} (hH : StronglyMeasurable[Filtration.natural B hm s] H) :
    IndepFun (fun ω => B t ω - B s ω) H P := by
  have hind : Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance)
      (Filtration.natural B hm s) P := by
    rw [Filtration.natural_eq_comap]
    exact preBrownian_increment_indep_past hB hst
  exact indep_of_indep_of_le_right hind hH.measurable.comap_le

theorem preBrownian_predictable_mul_memLp_two
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t)) {s t : ℝ≥0} (hst : s ≤ t)
    {H : Ω → ℝ} (hH : StronglyMeasurable[Filtration.natural B hm s] H)
    (hH2 : MemLp H 2 P) :
    MemLp (fun ω => H ω * (B t ω - B s ω)) 2 P := by
  have hD2 : MemLp (fun ω => B t ω - B s ω) 2 P := by
    simpa only [Pi.sub_def] using
      (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two.sub
        (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  have hind := (preBrownian_increment_indep_of_past_measurable hB hm hst hH).symm
  have hintsq := (hind.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)).integrable_mul
    hH2.integrable_sq hD2.integrable_sq
  apply (memLp_two_iff_integrable_sq (hH2.aestronglyMeasurable.mul hD2.aestronglyMeasurable)).2
  simpa only [Function.comp_def, Pi.mul_def, mul_pow, id_eq] using hintsq

theorem preBrownian_predictable_sum_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[Filtration.natural B hm (t i)] (H i))
    (hH2 : ∀ i, MemLp (H i) 2 P) (s : Finset ℕ) :
    ∫ ω, (∑ i ∈ s, H i ω * (B (t (i + 1)) ω - B (t i) ω)) ^ 2 ∂P =
      ∑ i ∈ s, ((t (i + 1) : ℝ) - (t i : ℝ)) * ∫ ω, H i ω ^ 2 ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let ℱ : Filtration ℕ mΩ :=
    ⟨fun i => Filtration.natural B hm (t i),
      fun _ _ hij => (Filtration.natural B hm).mono (ht hij),
      fun i => (Filtration.natural B hm).le (t i)⟩
  let D : ℕ → Ω → ℝ := fun i ω => B (t (i + 1)) ω - B (t i) ω
  have hD : ∀ i, StronglyMeasurable[ℱ (i + 1)] (D i) := by
    intro i
    exact (Filtration.stronglyAdapted_natural hm (t (i + 1))).sub
      ((Filtration.stronglyAdapted_natural hm (t i)).mono
        ((Filtration.natural B hm).mono (ht (Nat.le_succ i))))
  have hD2 : ∀ i, MemLp (D i) 2 P := by
    intro i
    exact (hB.isGaussianProcess.hasGaussianLaw_eval (t (i + 1))).memLp_two.sub
      (hB.isGaussianProcess.hasGaussianLaw_eval (t i)).memLp_two
  exact SimpleIntegral.predictable_sum_isometry ℱ H D
    (fun i => (t (i + 1) : ℝ) - (t i : ℝ)) hH hD hD2
    (fun i => preBrownian_predictable_mul_memLp_two hB hm (ht (Nat.le_succ i)) (hH i) (hH2 i))
    (fun i => preBrownian_increment_condExp_zero hB hm (ht (Nat.le_succ i)))
    (fun i => preBrownian_increment_sq_condExp hB hm (ht (Nat.le_succ i))) s

end Problem367

end OAI
