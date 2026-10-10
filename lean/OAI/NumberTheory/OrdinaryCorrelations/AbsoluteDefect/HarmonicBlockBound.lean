import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.WeightedPartialSumBound

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinaryDyadicHarmonic
open Finset

lemma harmonic_block_bound (a : ℕ → ℂ) {M : ℕ} (hM : 0 < M)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (ha : ∀ L, M ≤ L → L ≤ 2*M → ‖∑ n ∈ Finset.range L, a n‖ ≤ δ*L) :
    ‖∑ n ∈ Finset.range M, (((M+n+1 : ℕ):ℂ)⁻¹)*a (M+n)‖ ≤ 6*δ := by
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  have hp (j : ℕ) (hj : j ≤ M) :
      ‖∑ n ∈ Finset.range j, a (M+n)‖ ≤ 3*δ*M := by
    have he := sum_range_add a M j
    have he' : (∑ n ∈ Finset.range j, a (M+n)) =
        (∑ n ∈ Finset.range (M+j), a n) - ∑ n ∈ Finset.range M, a n := by
      rw [he]; abel
    rw [he']
    apply (norm_sub_le _ _).trans
    have hjr : (j:ℝ) ≤ M := by exact_mod_cast hj
    have h1 := ha (M+j) (by omega) (by omega)
    have h2 := ha M le_rfl (by omega)
    push_cast at h1
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hjr)]
  have hw (n : ℕ) : |((M+n+1:ℕ):ℝ)⁻¹| ≤ (M:ℝ)⁻¹ := by
    rw [abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
    exact inv_anti₀ hMr (by exact_mod_cast (show M ≤ M+n+1 by omega))
  have hv (n : ℕ) :
      |((M+(n+1)+1:ℕ):ℝ)⁻¹ - ((M+n+1:ℕ):ℝ)⁻¹| ≤ ((M:ℝ)⁻¹)^2 := by
    have hx : (0:ℝ) < ((M+n+1:ℕ):ℝ) := by positivity
    have hy : (0:ℝ) < ((M+(n+1)+1:ℕ):ℝ) := by positivity
    have hxy : ((M+n+1:ℕ):ℝ) ≤ ((M+(n+1)+1:ℕ):ℝ) := by push_cast; linarith
    rw [abs_of_nonpos (sub_nonpos.mpr (inv_anti₀ hx hxy))]
    have he : -(((M+(n+1)+1:ℕ):ℝ)⁻¹ - ((M+n+1:ℕ):ℝ)⁻¹) =
        ((M+(n+1)+1:ℕ):ℝ)⁻¹ * ((M+n+1:ℕ):ℝ)⁻¹ := by
      field_simp
      push_cast
      ring
    rw [he, pow_two]
    have hh := mul_le_mul (hw (n+1)) (hw n) (by positivity) (by positivity)
    simpa only [abs_of_pos (inv_pos.mpr hx), abs_of_pos (inv_pos.mpr hy)] using hh
  have hb := OrdinaryLogIntegral.weighted_partial_sum_bound
    (fun n => ((M+n+1:ℕ):ℝ)⁻¹) (fun n => a (M+n)) M
    (show 0 ≤ 3*δ*M by positivity) (show 0 ≤ ((M:ℝ)⁻¹)^2 by positivity)
    (show 0 ≤ (M:ℝ)⁻¹ by positivity) (hw (M-1)) (fun n hn => hv n) hp
  have he : ((M:ℝ)⁻¹+(M:ℝ)*((M:ℝ)⁻¹)^2)*(3*δ*M) = 6*δ := by
    field_simp
    ring
  rw [he] at hb
  simpa only [Complex.ofReal_inv, Complex.ofReal_natCast] using hb

lemma harmonic_segment_range_bound (a : ℕ → ℂ) {M K : ℕ} (hM : 0 < M) (hK : K ≤ M)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (ha : ∀ L, M ≤ L → L ≤ 2*M → ‖∑ n ∈ Finset.range L, a n‖ ≤ δ*L) :
    ‖∑ n ∈ Finset.range K, (((M+n+1 : ℕ):ℂ)⁻¹)*a (M+n)‖ ≤ 6*δ := by
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  have hp (j : ℕ) (hj : j ≤ M) :
      ‖∑ n ∈ Finset.range j, a (M+n)‖ ≤ 3*δ*M := by
    have he := sum_range_add a M j
    have he' : (∑ n ∈ Finset.range j, a (M+n)) =
        (∑ n ∈ Finset.range (M+j), a n) - ∑ n ∈ Finset.range M, a n := by
      rw [he]; abel
    rw [he']
    apply (norm_sub_le _ _).trans
    have hjr : (j:ℝ) ≤ M := by exact_mod_cast hj
    have h1 := ha (M+j) (by omega) (by omega)
    have h2 := ha M le_rfl (by omega)
    push_cast at h1
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hjr)]
  have hw (n : ℕ) : |((M+n+1:ℕ):ℝ)⁻¹| ≤ (M:ℝ)⁻¹ := by
    rw [abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
    exact inv_anti₀ hMr (by exact_mod_cast (show M ≤ M+n+1 by omega))
  have hv (n : ℕ) :
      |((M+(n+1)+1:ℕ):ℝ)⁻¹ - ((M+n+1:ℕ):ℝ)⁻¹| ≤ ((M:ℝ)⁻¹)^2 := by
    have hx : (0:ℝ) < ((M+n+1:ℕ):ℝ) := by positivity
    have hy : (0:ℝ) < ((M+(n+1)+1:ℕ):ℝ) := by positivity
    have hxy : ((M+n+1:ℕ):ℝ) ≤ ((M+(n+1)+1:ℕ):ℝ) := by push_cast; linarith
    rw [abs_of_nonpos (sub_nonpos.mpr (inv_anti₀ hx hxy))]
    have he : -(((M+(n+1)+1:ℕ):ℝ)⁻¹ - ((M+n+1:ℕ):ℝ)⁻¹) =
        ((M+(n+1)+1:ℕ):ℝ)⁻¹ * ((M+n+1:ℕ):ℝ)⁻¹ := by
      field_simp
      push_cast
      ring
    rw [he, pow_two]
    have hh := mul_le_mul (hw (n+1)) (hw n) (by positivity) (by positivity)
    simpa only [abs_of_pos (inv_pos.mpr hx), abs_of_pos (inv_pos.mpr hy)] using hh
  have hb := OrdinaryLogIntegral.weighted_partial_sum_bound
    (fun n => ((M+n+1:ℕ):ℝ)⁻¹) (fun n => a (M+n)) K
    (show 0 ≤ 3*δ*M by positivity) (show 0 ≤ ((M:ℝ)⁻¹)^2 by positivity)
    (show 0 ≤ (M:ℝ)⁻¹ by positivity) (hw (K-1)) (fun n hn => hv n) (fun j hj => hp j (hj.trans hK))
  have he : ((M:ℝ)⁻¹+(M:ℝ)*((M:ℝ)⁻¹)^2)*(3*δ*M) = 6*δ := by
    field_simp
    ring
  have hKr : (K:ℝ) ≤ M := by exact_mod_cast hK
  have hh : ((M:ℝ)⁻¹+(K:ℝ)*((M:ℝ)⁻¹)^2)*(3*δ*M) ≤ 6*δ := by
    rw [← he]
    gcongr
  apply le_trans ?_ hh
  simpa only [Complex.ofReal_inv, Complex.ofReal_natCast] using hb

lemma sum_range_shift (a : ℕ → ℂ) (M K : ℕ) :
    (∑ n ∈ Finset.range K, a (M+n+1)) = ∑ n ∈ Finset.Ioc M (M+K), a n := by
  apply sum_bij (fun n _ => M+n+1)
  · intro n hn; simp only [Finset.mem_range, Finset.mem_Ioc] at *; omega
  · intro n hn m hm he; omega
  · intro n hn
    refine ⟨n-M-1, ?_, ?_⟩ <;> simp only [Finset.mem_range, Finset.mem_Ioc] at * <;> omega
  · intro n hn; rfl

lemma sum_range_one (a : ℕ → ℂ) (K : ℕ) :
    (∑ n ∈ Finset.range K, a (n+1)) = ∑ n ∈ Finset.Icc 1 K, a n := by
  have he : Finset.Ioc 0 K = Finset.Icc 1 K := by ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  simpa only [zero_add, he] using sum_range_shift a 0 K

lemma harmonic_interval_bound (a : ℕ → ℂ) {M : ℕ} (hM : 0 < M)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (ha : ∀ L, M ≤ L → L ≤ 2*M → ‖∑ n ∈ Finset.Icc 1 L, a n‖ ≤ δ*L) :
    ‖∑ n ∈ Finset.Ioc M (2*M), ((n:ℂ)⁻¹)*a n‖ ≤ 6*δ := by
  have hh := harmonic_block_bound (fun n => a (n+1)) hM hδ
    (by simp_rw [sum_range_one]; exact ha)
  have he := sum_range_shift (fun n => ((n:ℂ)⁻¹)*a n) M M
  rw [show M+M=2*M by omega] at he
  exact he ▸ hh

lemma harmonic_segment_bound (a : ℕ → ℂ) {M L : ℕ} (hM : 0 < M)
    (hML : M ≤ L) (hL : L ≤ 2*M) {δ : ℝ} (hδ : 0 ≤ δ)
    (ha : ∀ J, M ≤ J → J ≤ 2*M → ‖∑ n ∈ Finset.Icc 1 J, a n‖ ≤ δ*J) :
    ‖∑ n ∈ Finset.Ioc M L, ((n:ℂ)⁻¹)*a n‖ ≤ 6*δ := by
  have hh := harmonic_segment_range_bound (fun n => a (n+1)) hM
    (show L-M ≤ M by omega) hδ (by simp_rw [sum_range_one]; exact ha)
  have he := sum_range_shift (fun n => ((n:ℂ)⁻¹)*a n) M (L-M)
  rw [Nat.add_sub_of_le hML] at he
  exact he ▸ hh

end OrdinaryDyadicHarmonic

end

end OAI
