import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367

theorem norm_sum_sq_le_card_mul_of_re_inner_rows
    {ι 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (s : Finset ι) (f : ι → E) {a : ι → ι → ℝ} {K : ℝ}
    (hinner : ∀ i ∈ s, ∀ j ∈ s, RCLike.re (inner 𝕜 (f i) (f j)) ≤ a i j)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, a i j ≤ K) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * K := by
  rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), sum_inner]
  simp_rw [inner_sum, map_sum]
  calc
    ∑ i ∈ s, ∑ j ∈ s, RCLike.re (inner 𝕜 (f i) (f j))
        ≤ ∑ i ∈ s, ∑ j ∈ s, a i j :=
      Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hinner i hi j hj
    _ ≤ ∑ _i ∈ s, K := Finset.sum_le_sum hrow
    _ = (s.card : ℝ) * K := by simp

theorem norm_sum_sq_le_card_mul_of_inner_rows
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Finset ι) (f : ι → E) {a : ι → ι → ℝ} {K : ℝ}
    (hinner : ∀ i ∈ s, ∀ j ∈ s, inner ℝ (f i) (f j) ≤ a i j)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, a i j ≤ K) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * K :=
  norm_sum_sq_le_card_mul_of_re_inner_rows (𝕜 := ℝ) s f hinner hrow

theorem sum_int_translate_le_tsum
    (s : Finset ℤ) (i : ℤ) {c : ℤ → ℝ}
    (hc : ∀ k, 0 ≤ c k) (hsum : Summable c) :
    ∑ j ∈ s, c (j - i) ≤ ∑' k, c k := by
  classical
  calc
    ∑ j ∈ s, c (j - i) = ∑ k ∈ s.image (fun j => j - i), c k := by
      symm
      apply Finset.sum_image
      intro a _ b _ hab
      exact sub_left_injective hab
    _ ≤ ∑' k, c k := Summable.sum_le_tsum _ (fun k _ => hc k) hsum

theorem norm_sum_sq_le_card_mul_tsum_kernel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Finset ℤ) (f : ℤ → E) {c : ℤ → ℝ} {S : ℝ}
    (hc : ∀ k, 0 ≤ c k) (hsum : Summable c) (hS : 0 ≤ S)
    (hinner : ∀ i ∈ s, ∀ j ∈ s,
      inner ℝ (f i) (f j) ≤ S * c (j - i)) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * (S * ∑' k, c k) := by
  apply norm_sum_sq_le_card_mul_of_inner_rows s f hinner
  intro i _
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_int_translate_le_tsum s i hc hsum) hS

def pathCorrelationKernel (q : ℝ) (k : ℤ) : ℝ :=
  ((k.natAbs : ℝ) + 1) * q ^ k.natAbs

theorem pathCorrelationKernel_nonneg {q : ℝ} (hq : 0 ≤ q) (k : ℤ) :
    0 ≤ pathCorrelationKernel q k := by
  unfold pathCorrelationKernel
  positivity

theorem summable_pathCorrelationKernel {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (pathCorrelationKernel q) := by
  have hn : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  have hlin : Summable (fun n : ℕ => (n : ℝ) * q ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have hgeom : Summable (fun n : ℕ => q ^ n) := summable_geometric_of_lt_one hq0 hq1
  have hnat : Summable (fun n : ℕ => ((n : ℝ) + 1) * q ^ n) := by
    simpa [add_mul] using hlin.add hgeom
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor <;> simpa [pathCorrelationKernel] using hnat

theorem tsum_pathCorrelationKernel {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' k, pathCorrelationKernel q k) = 2 / (1 - q) ^ 2 - 1 := by
  have hn : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  have hnat : HasSum (fun n : ℕ => ((n : ℝ) + 1) * q ^ n)
      (1 / (1 - q) ^ 2) := by
    simpa using hasSum_choose_mul_geometric_of_norm_lt_one 1 hn
  have hpos : HasSum (fun n : ℕ => pathCorrelationKernel q (n : ℤ))
      (1 / (1 - q) ^ 2) := by
    simpa [pathCorrelationKernel] using hnat
  have hneg : HasSum (fun n : ℕ => pathCorrelationKernel q (-(n : ℤ)))
      (1 / (1 - q) ^ 2) := by
    simpa [pathCorrelationKernel] using hnat
  have h := (hpos.of_nat_of_neg hneg).tsum_eq
  simpa [pathCorrelationKernel, ← two_mul, div_eq_mul_inv] using h

theorem norm_sum_sq_le_pathCorrelationKernel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Finset ℤ) (f : ℤ → E) {q S : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hS : 0 ≤ S)
    (hinner : ∀ i ∈ s, ∀ j ∈ s,
      inner ℝ (f i) (f j) ≤ S * pathCorrelationKernel q (j - i)) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤
      (s.card : ℝ) * (S * ∑' k, pathCorrelationKernel q k) :=
  norm_sum_sq_le_card_mul_tsum_kernel s f
    (pathCorrelationKernel_nonneg hq0) (summable_pathCorrelationKernel hq0 hq1) hS hinner

theorem norm_sum_sq_le_geometric_inner_bound
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (s : Finset ℤ) (f : ℤ → E) {q S : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hS : 0 ≤ S)
    (hinner : ∀ i ∈ s, ∀ j ∈ s,
      ‖inner 𝕜 (f i) (f j)‖ ≤ S * pathCorrelationKernel q (j - i)) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * S * (2 / (1 - q) ^ 2 - 1) := by
  have h := norm_sum_sq_le_card_mul_of_re_inner_rows s f
    (fun i hi j hj => (RCLike.re_le_norm _).trans (hinner i hi j hj))
    (K := S * ∑' k, pathCorrelationKernel q k) (fun i _ => by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_int_translate_le_tsum s i
        (pathCorrelationKernel_nonneg hq0) (summable_pathCorrelationKernel hq0 hq1)) hS)
  simpa [tsum_pathCorrelationKernel hq0 hq1, mul_assoc] using h

open MeasureTheory

theorem integral_sum_sq_eq_sum_pair_moments
    {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset ι) (f : ι → Ω → ℝ)
    (hf : ∀ i ∈ s, MemLp (f i) 2 μ) :
    (∫ ω, (∑ i ∈ s, f i ω) ^ 2 ∂μ) =
      ∑ i ∈ s, ∑ j ∈ s, ∫ ω, f i ω * f j ω ∂μ := by
  have hp : ∀ i ∈ s, ∀ j ∈ s, Integrable (fun ω => f i ω * f j ω) μ := by
    intro i hi j hj
    exact (hf i hi).integrable_mul (hf j hj)
  calc
    (∫ ω, (∑ i ∈ s, f i ω) ^ 2 ∂μ) =
        ∫ ω, ∑ i ∈ s, ∑ j ∈ s, f i ω * f j ω ∂μ := by
      congr 1
      funext ω
      rw [pow_two, Finset.sum_mul_sum]
    _ = ∑ i ∈ s, ∑ j ∈ s, ∫ ω, f i ω * f j ω ∂μ := by
      rw [integral_finsetSum s (fun i hi => integrable_finsetSum s (hp i hi))]
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_finsetSum s (hp i hi)

theorem integral_sum_sq_le_card_mul_of_pair_rows
    {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset ι) (f : ι → Ω → ℝ) {a : ι → ι → ℝ} {K : ℝ}
    (hf : ∀ i ∈ s, MemLp (f i) 2 μ)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, (∫ ω, f i ω * f j ω ∂μ) ≤ a i j)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, a i j ≤ K) :
    (∫ ω, (∑ i ∈ s, f i ω) ^ 2 ∂μ) ≤ (s.card : ℝ) * K := by
  rw [integral_sum_sq_eq_sum_pair_moments s f hf]
  calc
    ∑ i ∈ s, ∑ j ∈ s, ∫ ω, f i ω * f j ω ∂μ
        ≤ ∑ i ∈ s, ∑ j ∈ s, a i j :=
      Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hpair i hi j hj
    _ ≤ ∑ _i ∈ s, K := Finset.sum_le_sum hrow
    _ = (s.card : ℝ) * K := by simp

theorem integral_sum_sq_le_card_mul_tsum_kernel
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset ℤ) (f : ℤ → Ω → ℝ) {c : ℤ → ℝ} {S : ℝ}
    (hc : ∀ k, 0 ≤ c k) (hsum : Summable c) (hS : 0 ≤ S)
    (hf : ∀ i ∈ s, MemLp (f i) 2 μ)
    (hpair : ∀ i ∈ s, ∀ j ∈ s,
      (∫ ω, f i ω * f j ω ∂μ) ≤ S * c (j - i)) :
    (∫ ω, (∑ i ∈ s, f i ω) ^ 2 ∂μ) ≤
      (s.card : ℝ) * (S * ∑' k, c k) := by
  apply integral_sum_sq_le_card_mul_of_pair_rows s f hf hpair
  intro i _
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_int_translate_le_tsum s i hc hsum) hS

theorem integral_sum_sq_le_geometric_pair_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset ℤ) (f : ℤ → Ω → ℝ) {q S : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hS : 0 ≤ S)
    (hf : ∀ i ∈ s, MemLp (f i) 2 μ)
    (hpair : ∀ i ∈ s, ∀ j ∈ s,
      |∫ ω, f i ω * f j ω ∂μ| ≤ S * pathCorrelationKernel q (j - i)) :
    (∫ ω, (∑ i ∈ s, f i ω) ^ 2 ∂μ) ≤
      (s.card : ℝ) * S * (2 / (1 - q) ^ 2 - 1) := by
  have h := integral_sum_sq_le_card_mul_tsum_kernel s f
    (pathCorrelationKernel_nonneg hq0) (summable_pathCorrelationKernel hq0 hq1)
    hS hf (fun i hi j hj => (le_abs_self _).trans (hpair i hi j hj))
  simpa [tsum_pathCorrelationKernel hq0 hq1, mul_assoc] using h

end Problem367

end

end OAI
