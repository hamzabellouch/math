import OAI.Probability.FreeIsing.Martingales.BoundedMartingaleVariation
import OAI.Probability.FreeIsing.Martingales.QuadraticVariation
import OAI.Probability.FreeIsing.Stochastic.CompensatorVariation

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace Problem367.ContinuousMartingaleVariation

open MartingaleQuadraticVariation

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem tendsto_integral_weighted_error_sq [IsProbabilityMeasure μ]
    {I : Type*} [Preorder I] [PseudoMetricSpace I]
    {F : Filtration I mΩ} {M A : I → Ω → ℝ}
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => (M t ω) ^ 2 - A t ω) F μ)
    {C : ℝ} (hC : 0 ≤ C) (hMb : ∀ t, ∀ᵐ ω ∂μ, |M t ω| ≤ C)
    {S : Set I} (hS : IsCompact S)
    (hMc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => M t ω) S)
    (hAc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => A t ω) S)
    (t : ℕ → ℕ → I) (ht : ∀ n, Monotone (t n)) (N : ℕ → ℕ)
    (hmem : ∀ n i, i ≤ N n → t n i ∈ S) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hmesh : ∀ n i, i < N n → dist (t n (i + 1)) (t n i) ≤ δ n)
    (hApos : ∀ᵐ ω ∂μ, ∀ n i, i < N n →
      0 ≤ A (t n (i + 1)) ω - A (t n i) ω)
    {B : ℝ} (hB : 0 ≤ B)
    (hAb : ∀ᵐ ω ∂μ, ∀ n, A (t n (N n)) ω - A (t n 0) ω ≤ B)
    (H : ℕ → ℕ → Ω → ℝ)
    (hH : ∀ n i, i < N n → StronglyMeasurable[F (t n i)] (H n i))
    {L : ℝ} (hL : 0 ≤ L)
    (hHb : ∀ n i, i < N n → ∀ᵐ ω ∂μ, |H n i ω| ≤ L) :
    Tendsto (fun n => ∫ ω, (∑ i ∈ Finset.range (N n),
      H n i ω * squareError M A (t n i) (t n (i + 1)) ω) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  have hMm (s : I) : AEStronglyMeasurable (M s) μ :=
    ((hM.stronglyMeasurable s).mono (F.le s)).aestronglyMeasurable
  have hM2 (s : I) : MemLp (M s) 2 μ :=
    MemLp.of_bound (hMm s) C (by simpa only [Real.norm_eq_abs] using hMb s)
  have hAm (s : I) : AEStronglyMeasurable (A s) μ :=
    ((stronglyAdapted_compensator hM hQ s).mono (F.le s)).aestronglyMeasurable
  have hD4 (n i : ℕ) (_hi : i < N n) :
      MemLp (fun ω => (increment M (t n i) (t n (i + 1)) ω) ^ 2) 2 μ := by
    apply BoundedMartingaleVariation.bounded_pow_memLp_two
      ((hMm (t n (i + 1))).sub (hMm (t n i))) (show 0 ≤ 2 * C by positivity) ?_ 2
    filter_upwards [hMb (t n (i + 1)), hMb (t n i)] with ω hn hi
    exact (abs_sub _ _).trans (by linarith)
  have hA2 (n i : ℕ) (hi : i < N n) :
      MemLp (increment A (t n i) (t n (i + 1))) 2 μ :=
    CompensatorVariation.memLp_increment_of_total_bound (fun j => hAm (t n j))
      (hApos.mono (fun ω hω => hω n)) (hAb.mono (fun ω hω => hω n)) hi 2
  have hfour := BoundedMartingaleVariation.tendsto_sum_integral_fourth_of_continuous
    hM hC hMb hS hMc t ht N hmem δ hδ hmesh
  have hcomp := CompensatorVariation.tendsto_sum_integral_sq_increments
    hS hAm hAc t N δ hmem
    (fun n i hi => by simpa only [dist_comm] using hmesh n i hi) hδ hApos hB hAb
  exact tendsto_integral_finite_grid_weighted_error_sq hM hQ hM2 t ht N H hH
    hD4 hA2 hL hHb hfour hcomp

theorem tendsto_integral_weighted_error_sq_of_monotone [IsProbabilityMeasure μ]
    {I : Type*} [Preorder I] [PseudoMetricSpace I]
    {F : Filtration I mΩ} {M A : I → Ω → ℝ}
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => (M t ω) ^ 2 - A t ω) F μ)
    {C : ℝ} (hC : 0 ≤ C) (hMb : ∀ t, ∀ᵐ ω ∂μ, |M t ω| ≤ C)
    {S : Set I} (hS : IsCompact S)
    (hMc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => M t ω) S)
    (hAc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => A t ω) S)
    (hAmono : ∀ᵐ ω ∂μ, MonotoneOn (fun t => A t ω) S)
    (t : ℕ → ℕ → I) (ht : ∀ n, Monotone (t n)) (N : ℕ → ℕ)
    (hmem : ∀ n i, i ≤ N n → t n i ∈ S) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hmesh : ∀ n i, i < N n → dist (t n (i + 1)) (t n i) ≤ δ n)
    {B : ℝ} (hB : 0 ≤ B)
    (hAb : ∀ᵐ ω ∂μ, ∀ n, A (t n (N n)) ω - A (t n 0) ω ≤ B)
    (H : ℕ → ℕ → Ω → ℝ)
    (hH : ∀ n i, i < N n → StronglyMeasurable[F (t n i)] (H n i))
    {L : ℝ} (hL : 0 ≤ L)
    (hHb : ∀ n i, i < N n → ∀ᵐ ω ∂μ, |H n i ω| ≤ L) :
    Tendsto (fun n => ∫ ω, (∑ i ∈ Finset.range (N n),
      H n i ω * squareError M A (t n i) (t n (i + 1)) ω) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  apply tendsto_integral_weighted_error_sq hM hQ hC hMb hS hMc hAc t ht N hmem δ hδ
    hmesh ?_ hB hAb H hH hL hHb
  filter_upwards [hAmono] with ω hω
  intro n i hi
  exact sub_nonneg.mpr (hω (hmem n i hi.le) (hmem n (i + 1) (Nat.succ_le_of_lt hi))
    (ht n (Nat.le_succ i)))

end Problem367.ContinuousMartingaleVariation

end

end OAI
