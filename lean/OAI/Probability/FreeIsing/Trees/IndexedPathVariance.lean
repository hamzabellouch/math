import OAI.Probability.FreeIsing.Trees.PathVariance

namespace OAI

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Problem367

theorem sum_indexed_translate_le_tsum {ι : Type*}
    (s : Finset ι) (z : ι → ℤ) (hz : Set.InjOn z (s : Set ι))
    (i : ℤ) {c : ℤ → ℝ} (hc : ∀ k, 0 ≤ c k) (hsum : Summable c) :
    ∑ j ∈ s, c (z j - i) ≤ ∑' k, c k := by
  classical
  calc
    ∑ j ∈ s, c (z j - i) = ∑ k ∈ s.image (fun j => z j - i), c k := by
      symm
      apply Finset.sum_image
      intro a ha b hb hab
      apply hz ha hb
      exact sub_left_injective hab
    _ ≤ ∑' k, c k := Summable.sum_le_tsum _ (fun k _ => hc k) hsum

theorem norm_sum_sq_le_geometric_bound_of_injective_index
    {ι 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (s : Finset ι) (z : ι → ℤ) (hz : Set.InjOn z (s : Set ι))
    (f : ι → E) {q S : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hS : 0 ≤ S)
    (hinner : ∀ i ∈ s, ∀ j ∈ s,
      ‖inner 𝕜 (f i) (f j)‖ ≤ S * pathCorrelationKernel q (z j - z i)) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * S * (2 / (1 - q) ^ 2 - 1) := by
  have h := norm_sum_sq_le_card_mul_of_re_inner_rows s f
    (fun i hi j hj => (RCLike.re_le_norm _).trans (hinner i hi j hj))
    (K := S * ∑' k, pathCorrelationKernel q k) (fun i _ => by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_indexed_translate_le_tsum s z hz (z i)
        (pathCorrelationKernel_nonneg hq0) (summable_pathCorrelationKernel hq0 hq1)) hS)
  simpa only [tsum_pathCorrelationKernel hq0 hq1, mul_assoc] using h

theorem integral_sum_sq_le_geometric_bound_of_injective_index
    {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset ι) (z : ι → ℤ) (hz : Set.InjOn z (s : Set ι))
    (f : ι → Ω → ℝ) {q S : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hS : 0 ≤ S)
    (hf : ∀ i ∈ s, MemLp (f i) 2 μ)
    (hpair : ∀ i ∈ s, ∀ j ∈ s,
      |∫ ω, f i ω * f j ω ∂μ| ≤ S * pathCorrelationKernel q (z j - z i)) :
    (∫ ω, (∑ i ∈ s, f i ω) ^ 2 ∂μ) ≤
      (s.card : ℝ) * S * (2 / (1 - q) ^ 2 - 1) := by
  have h := integral_sum_sq_le_card_mul_of_pair_rows s f hf
    (fun i hi j hj => (le_abs_self _).trans (hpair i hi j hj))
    (K := S * ∑' k, pathCorrelationKernel q k) (fun i _ => by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_indexed_translate_le_tsum s z hz (z i)
        (pathCorrelationKernel_nonneg hq0) (summable_pathCorrelationKernel hq0 hq1)) hS)
  simpa only [tsum_pathCorrelationKernel hq0 hq1, mul_assoc] using h

theorem norm_sum_fin_sq_le_geometric_inner_bound
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {n : ℕ} (f : Fin n → E) {q S : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hS : 0 ≤ S)
    (hinner : ∀ i j, ‖inner 𝕜 (f i) (f j)‖ ≤
      S * pathCorrelationKernel q ((j : ℤ) - (i : ℤ))) :
    ‖∑ i, f i‖ ^ 2 ≤ (n : ℝ) * S * (2 / (1 - q) ^ 2 - 1) := by
  have hinj : Function.Injective (fun i : Fin n => (i : ℤ)) := by
    intro i j hij
    exact Fin.ext (Int.ofNat.inj hij)
  simpa using norm_sum_sq_le_geometric_bound_of_injective_index
    Finset.univ (fun i : Fin n => (i : ℤ)) hinj.injOn f hq0 hq1 hS
    (fun i _ j _ => hinner i j)

theorem integral_sum_fin_sq_le_geometric_pair_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {n : ℕ} (f : Fin n → Ω → ℝ) {q S : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hS : 0 ≤ S)
    (hf : ∀ i, MemLp (f i) 2 μ)
    (hpair : ∀ i j, |∫ ω, f i ω * f j ω ∂μ| ≤
      S * pathCorrelationKernel q ((j : ℤ) - (i : ℤ))) :
    (∫ ω, (∑ i, f i ω) ^ 2 ∂μ) ≤
      (n : ℝ) * S * (2 / (1 - q) ^ 2 - 1) := by
  have hinj : Function.Injective (fun i : Fin n => (i : ℤ)) := by
    intro i j hij
    exact Fin.ext (Int.ofNat.inj hij)
  simpa using integral_sum_sq_le_geometric_bound_of_injective_index
    Finset.univ (fun i : Fin n => (i : ℤ)) hinj.injOn f hq0 hq1 hS
    (fun i _ => hf i) (fun i _ j _ => hpair i j)

theorem norm_sum_fin_sq_le_ordered_geometric_inner_bound
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {n : ℕ} (f : Fin n → E) {q S : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hS : 0 ≤ S)
    (hinner : ∀ i j, i ≤ j → ‖inner 𝕜 (f i) (f j)‖ ≤
      S * (((j.val - i.val : ℕ) : ℝ) + 1) * q ^ (j.val - i.val)) :
    ‖∑ i, f i‖ ^ 2 ≤ (n : ℝ) * S * (2 / (1 - q) ^ 2 - 1) := by
  apply norm_sum_fin_sq_le_geometric_inner_bound (𝕜 := 𝕜) f hq0 hq1 hS
  intro i j
  by_cases hij : i ≤ j
  · simpa only [pathCorrelationKernel,
      Int.natAbs_natCast_sub_natCast_of_ge hij, mul_assoc] using hinner i j hij
  · have hji : j ≤ i := le_of_not_ge hij
    rw [norm_inner_symm]
    simpa only [pathCorrelationKernel,
      Int.natAbs_natCast_sub_natCast_of_le hji, mul_assoc] using hinner j i hji

theorem integral_sum_fin_sq_le_ordered_geometric_pair_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {n : ℕ} (f : Fin n → Ω → ℝ) {q S : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hS : 0 ≤ S)
    (hf : ∀ i, MemLp (f i) 2 μ)
    (hpair : ∀ i j, i ≤ j → |∫ ω, f i ω * f j ω ∂μ| ≤
      S * (((j.val - i.val : ℕ) : ℝ) + 1) * q ^ (j.val - i.val)) :
    (∫ ω, (∑ i, f i ω) ^ 2 ∂μ) ≤
      (n : ℝ) * S * (2 / (1 - q) ^ 2 - 1) := by
  apply integral_sum_fin_sq_le_geometric_pair_bound f hq0 hq1 hS hf
  intro i j
  by_cases hij : i ≤ j
  · simpa only [pathCorrelationKernel,
      Int.natAbs_natCast_sub_natCast_of_ge hij, mul_assoc] using hpair i j hij
  · have hji : j ≤ i := le_of_not_ge hij
    have heq : (∫ ω, f i ω * f j ω ∂μ) = ∫ ω, f j ω * f i ω ∂μ := by
      congr 1
      funext ω
      exact mul_comm _ _
    rw [heq]
    simpa only [pathCorrelationKernel,
      Int.natAbs_natCast_sub_natCast_of_le hji, mul_assoc] using hpair j i hji

end Problem367

end

end OAI
