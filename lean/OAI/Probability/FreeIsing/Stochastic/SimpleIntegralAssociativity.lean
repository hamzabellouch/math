import OAI.Probability.FreeIsing.Brownian.FiltrationIntegral
import OAI.Probability.FreeIsing.Brownian.GridRefinement

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.BrownianGrid

theorem integralSum_succ_sub {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (H : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    integralSum B t H (n + 1) ω - integralSum B t H n ω =
      H n ω * (B (t (n + 1)) ω - B (t n) ω) := by
  simp only [integralSum, Finset.sum_range_succ, add_sub_cancel_left]

theorem integralSum_compose {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (H K : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    (∑ i ∈ Finset.range n, K i ω *
      (integralSum B t H (i + 1) ω - integralSum B t H i ω)) =
      integralSum B t (fun i ω => K i ω * H i ω) n ω := by
  simp_rw [integralSum_succ_sub]
  simp only [integralSum, mul_assoc]

theorem integralSum_compose_refined {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (H K : ℕ → Ω → ℝ) (n : ℕ) {k : ℕ}
    (hk : 0 < k) (ω : Ω) :
    (∑ j ∈ Finset.range n, K j ω *
      (integralSum B t H ((j + 1) * k) ω - integralSum B t H (j * k) ω)) =
      integralSum B t (fun i ω => K (i / k) ω * H i ω) (n * k) ω := by
  rw [weighted_sum_refinement (fun i => integralSum B t H i ω)
    (fun j => K j ω) n hk]
  simp_rw [integralSum_succ_sub]
  simp only [integralSum, mul_assoc]

theorem stronglyMeasurable_compose_refined
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (F : Filtration ℝ≥0 mΩ)
    {t : ℕ → ℝ≥0} (ht : Monotone t) {H K : ℕ → Ω → ℝ} {k : ℕ}
    (hH : ∀ i, StronglyMeasurable[F (t i)] (H i))
    (hK : ∀ j, StronglyMeasurable[F (t (j * k))] (K j)) (i : ℕ) :
    StronglyMeasurable[F (t i)] (fun ω => K (i / k) ω * H i ω) :=
  ((hK (i / k)).mono (F.mono (ht (Nat.div_mul_le_self i k)))).mul (hH i)

theorem memLp_compose_of_bounded
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {H K : Ω → ℝ} (hH : MemLp H 2 P) (hK : AEStronglyMeasurable K P)
    {C : ℝ} (hb : ∀ᵐ ω ∂P, |K ω| ≤ C) :
    MemLp (fun ω => K ω * H ω) 2 P := by
  apply hH.of_le_mul (c := C) (hK.mul hH.aestronglyMeasurable)
  filter_upwards [hb] with ω hω
  simpa only [Real.norm_eq_abs, Pi.mul_apply, abs_mul] using
    mul_le_mul_of_nonneg_right hω (abs_nonneg (H ω))

theorem composed_integralSum_difference_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H K J : ℕ → Ω → ℝ)
    {k : ℕ} (hk : 0 < k)
    (hH : ∀ i, StronglyMeasurable[F (t i)] (H i))
    (hK : ∀ j, StronglyMeasurable[F (t (j * k))] (K j))
    (hJ : ∀ i, StronglyMeasurable[F (t i)] (J i))
    (hKH2 : ∀ i, MemLp (fun ω => K (i / k) ω * H i ω) 2 P)
    (hJ2 : ∀ i, MemLp (J i) 2 P) (n : ℕ) :
    (∫ ω, ((∑ j ∈ Finset.range n, K j ω *
      (integralSum B t H ((j + 1) * k) ω - integralSum B t H (j * k) ω)) -
        integralSum B t J (n * k) ω) ^ 2 ∂P) =
      ∑ i ∈ Finset.range (n * k), ((t (i + 1) : ℝ) - (t i : ℝ)) *
        ∫ ω, (K (i / k) ω * H i ω - J i ω) ^ 2 ∂P := by
  simp_rw [integralSum_compose_refined B t H K n hk]
  simpa only [integralSum, sub_mul, Finset.sum_sub_distrib] using
    BrownianFiltration.predictable_sum_isometry hB hAd hind t ht
      (fun i ω => K (i / k) ω * H i ω - J i ω)
      (fun i => (stronglyMeasurable_compose_refined F ht hH hK i).sub (hJ i))
      (fun i => (hKH2 i).sub (hJ2 i)) (Finset.range (n * k))

theorem composed_integralSum_difference_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H K J : ℕ → Ω → ℝ)
    {k : ℕ} (hk : 0 < k)
    (hH : ∀ i, StronglyMeasurable[F (t i)] (H i))
    (hK : ∀ j, StronglyMeasurable[F (t (j * k))] (K j))
    (hJ : ∀ i, StronglyMeasurable[F (t i)] (J i))
    (hKH2 : ∀ i, MemLp (fun ω => K (i / k) ω * H i ω) 2 P)
    (hJ2 : ∀ i, MemLp (J i) 2 P) (n : ℕ) {ε : ℝ}
    (happrox : ∀ i < n * k,
      (∫ ω, (K (i / k) ω * H i ω - J i ω) ^ 2 ∂P) ≤ ε) :
    (∫ ω, ((∑ j ∈ Finset.range n, K j ω *
      (integralSum B t H ((j + 1) * k) ω - integralSum B t H (j * k) ω)) -
        integralSum B t J (n * k) ω) ^ 2 ∂P) ≤
      ((t (n * k) : ℝ) - (t 0 : ℝ)) * ε := by
  rw [composed_integralSum_difference_isometry hB hAd hind t ht H K J hk
    hH hK hJ hKH2 hJ2 n]
  calc
    _ ≤ ∑ i ∈ Finset.range (n * k), ((t (i + 1) : ℝ) - (t i : ℝ)) * ε := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (happrox i (Finset.mem_range.mp hi))
        (sub_nonneg.mpr (NNReal.coe_le_coe.mpr (ht (Nat.le_succ i))))
    _ = _ := by
      rw [← Finset.sum_mul, Finset.sum_range_sub (fun i => (t i : ℝ)) (n * k)]

end Problem367.BrownianGrid

end

end OAI
