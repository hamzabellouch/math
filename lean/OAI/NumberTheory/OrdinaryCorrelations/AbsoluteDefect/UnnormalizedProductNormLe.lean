import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.CoefficientHom
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.RealPowerHom

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter

namespace OrdinaryCorrelations.PretentiousEuler
open Finset Completion NonpretentiousEuler

lemma unnormalized_product_norm_le {ι : Type*} (s : Finset ι) (r : ι → ℝ) (z : ι → ℂ)
    (hr : ∀ i ∈ s, 0 ≤ r i) (hr1 : ∀ i ∈ s, r i ≤ 1/2)
    (hz : ∀ i ∈ s, ‖z i‖ ≤ 1) :
    ‖∏ i ∈ s, (1-(r i:ℂ)*z i)⁻¹‖ ≤
      (∏ i ∈ s, (1-r i)⁻¹) *
        Real.exp (-(∑ i ∈ s, r i*(1-(z i).re)) + ∑ i ∈ s, (r i)^2) := by
  have hd : 0 < ∏ i ∈ s, (1-r i) := prod_pos (fun i hi => by linarith [hr1 i hi])
  have he : ‖∏ i ∈ s, factor (r i) (z i)‖ =
      (∏ i ∈ s, (1-r i)) * ‖∏ i ∈ s, (1-(r i:ℂ)*z i)⁻¹‖ := by
    rw [norm_prod,norm_prod,←prod_mul_distrib]
    apply prod_congr rfl
    intro i hi
    rw [factor,norm_mul]
    congr 1
    rw [←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (by linarith [hr1 i hi] : 0 ≤ 1-r i)]
  have hh := product_norm_le s r z hr hr1 hz
  rw [he] at hh
  rw [prod_inv_distrib (fun i => (1-r i))]
  calc
    _ = (∏ i ∈ s, (1-r i))⁻¹ *
        ((∏ i ∈ s, (1-r i)) * ‖∏ i ∈ s, (1-(r i:ℂ)*z i)⁻¹‖) := by
      rw [←mul_assoc,inv_mul_cancel₀ hd.ne',one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hd.le)

lemma weighted_cutoff_distance {f : ℕ → ℂ} (hf : OneBounded f) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) {N K : ℕ} (hN : 2 ≤ N) (hK : N < K) :
    Real.exp (-1) * distanceSq f χ t N ≤
      ∑ p ∈ K.primesBelow, (p:ℝ)^(-(1+1/Real.log N))*(1-(twist f χ t p).re) := by
  let P := (Icc 2 N).filter Nat.Prime
  have hsub : P ⊆ K.primesBelow := by
    intro p hp
    obtain ⟨hpI,hpp⟩ := mem_filter.mp hp
    obtain ⟨hp2,hpN⟩ := mem_Icc.mp hpI
    exact Nat.mem_primesBelow.mpr ⟨lt_of_le_of_lt hpN hK,hpp⟩
  have hre (p : ℕ) : 0 ≤ 1-(twist f χ t p).re := by
    have hle := (Complex.re_le_norm (twist f χ t p)).trans (twist_norm_le hf χ t p)
    linarith
  calc
    _ = ∑ p ∈ P, (Real.exp (-1)/(p:ℝ))*(1-(twist f χ t p).re) := by
      simp only [distanceSq,Nat.floor_natCast,mul_sum]
      apply sum_congr rfl
      intro p hp
      change Real.exp (-1)*((1-(twist f χ t p).re)/(p:ℝ)) = _
      ring
    _ ≤ ∑ p ∈ P, (p:ℝ)^(-(1+1/Real.log N))*(1-(twist f χ t p).re) := by
      apply sum_le_sum
      intro p hp
      have hpN := (mem_Icc.mp (mem_filter.mp hp).1).2
      have hpp := (mem_filter.mp hp).2
      exact mul_le_mul_of_nonneg_right (cutoff_negativePower_lower hN hpp.pos hpN) (hre p)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ =>
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _) (hre p))

theorem regularized_series_norm_le {f : ℕ → ℂ} (hf : OneBounded f) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    ‖∑' n : ℕ, complete (twist f χ t) n * (↑((n:ℝ)^(-(1+1/Real.log N))):ℂ)‖ ≤
      (∑' n : ℕ, (n:ℝ)^(-(1+1/Real.log N))) *
        Real.exp (1-Real.exp (-1)*distanceSq f χ t N) := by
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hσ : 1 < 1+1/Real.log N := lt_add_of_pos_right _ (one_div_pos.mpr hlog)
  have h1 := (weighted_euler_tendsto (twist_norm_le hf χ t) hσ).norm
  have h2 := (realPower_euler_tendsto hσ).mul_const (Real.exp (1-Real.exp (-1)*distanceSq f χ t N))
  apply le_of_tendsto_of_tendsto h1 h2
  filter_upwards [eventually_gt_atTop N] with K hK
  have hK1 : 1 ≤ K := by omega
  have hnorm := unnormalized_product_norm_le K.primesBelow
    (fun p => (p:ℝ)^(-(1+1/Real.log N))) (twist f χ t)
    (fun p hp => Real.rpow_nonneg (Nat.cast_nonneg p) _)
    (fun p hp => prime_weight_half hσ.le (Nat.mem_primesBelow.mp hp).2)
    (fun p hp => twist_norm_le hf χ t p)
  refine hnorm.trans ?_
  apply mul_le_mul_of_nonneg_left
  · apply Real.exp_le_exp.mpr
    have hd := weighted_cutoff_distance hf χ t hN hK
    have hs := prime_weight_squares_le hσ.le hK1
    linarith
  · apply prod_nonneg
    intro p hp
    apply inv_nonneg.mpr
    have he := prime_weight_half hσ.le (Nat.mem_primesBelow.mp hp).2
    linarith

def regularizedSeries (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (N : ℕ) : ℂ :=
  ∑' n : ℕ, complete f n * star (χ (n : ZMod q) *
    Complex.exp (((t * Real.log n):ℝ) * Complex.I)) * (↑((n:ℝ)^(-(1+1/Real.log N))):ℂ)

theorem regularizedSeries_norm_le {f : ℕ → ℂ} (hf : OneBounded f) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    ‖regularizedSeries f χ t N‖ ≤ (∑' n : ℕ, (n:ℝ)^(-(1+1/Real.log N))) *
      Real.exp (1-Real.exp (-1)*distanceSq f χ t N) := by
  simpa only [complete_twist,twist,regularizedSeries] using regularized_series_norm_le hf χ t hN

theorem eventual_uniform_regularizedSeries {f : ℕ → ℂ} (hf : OneBounded f)
    (hNP : UniformlyNonpretentious f) (q : ℕ) (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ t ∈ Set.Icc (-(N:ℝ)) (N:ℝ),
      ‖regularizedSeries f χ t N‖ ≤ ε * (∑' n : ℕ, (n:ℝ)^(-(1+1/Real.log N))) := by
  filter_upwards [eventual_distanceSq_lower hf hNP q hq χ ((1-Real.log ε)/Real.exp (-1)),
    eventually_ge_atTop (2:ℕ)] with N hN hN2
  intro t ht
  have he : Real.exp (1-Real.exp (-1)*distanceSq f χ t N) ≤ ε := by
    rw [←Real.exp_log hε]
    apply Real.exp_le_exp.mpr
    have hd := (div_le_iff₀ (Real.exp_pos (-1))).mp (hN t ht)
    linarith
  calc
    _ ≤ _ := regularizedSeries_norm_le hf χ t hN2
    _ ≤ _ := by
      rw [mul_comm ε]
      exact mul_le_mul_of_nonneg_left he (tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _))

end OrdinaryCorrelations.PretentiousEuler

end

end OAI
