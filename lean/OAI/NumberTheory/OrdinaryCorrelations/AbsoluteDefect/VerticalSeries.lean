import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.UnnormalizedProductNormLe

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

def verticalSeries (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) : ℂ :=
  ∑' n : ℕ, complete f n * star (χ (n : ZMod q) *
    Complex.exp (((t * Real.log n):ℝ) * Complex.I)) * (↑((n:ℝ)^(-σ)):ℂ)

lemma cutoff_power_lower {N p : ℕ} (hN : 2≤N) (hp : 0<p) (hpN : p≤N)
    {σ : ℝ} (hσ : σ ≤ 1+1/Real.log N) :
    Real.exp (-1)/(p:ℝ) ≤ (p:ℝ)^(-σ) := by
  apply (cutoff_negativePower_lower hN hp hpN).trans
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast hp
  · linarith

lemma weighted_distance_lower {f : ℕ → ℂ} (hf : OneBounded f) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) {N K : ℕ} (hN : 2≤N) (hK : N<K)
    {σ : ℝ} (hσ : σ ≤ 1+1/Real.log N) :
    Real.exp (-1)*distanceSq f χ t N ≤
      ∑ p ∈ K.primesBelow, (p:ℝ)^(-σ)*(1-(twist f χ t p).re) := by
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
    _ ≤ ∑ p ∈ P, (p:ℝ)^(-σ)*(1-(twist f χ t p).re) := by
      apply sum_le_sum
      intro p hp
      have hpN := (mem_Icc.mp (mem_filter.mp hp).1).2
      have hpp := (mem_filter.mp hp).2
      exact mul_le_mul_of_nonneg_right (cutoff_power_lower hN hpp.pos hpN hσ) (hre p)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ =>
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _) (hre p))

theorem vertical_series_norm_le {f : ℕ → ℂ} (hf : OneBounded f) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) {N : ℕ} (hN : 2≤N)
    {σ : ℝ} (hσ : 1<σ) (hσN : σ≤1+1/Real.log N) :
    ‖verticalSeries f χ σ t‖ ≤ (∑' n : ℕ, (n:ℝ)^(-σ)) *
      Real.exp (1-Real.exp (-1)*distanceSq f χ t N) := by
  have h1 := (weighted_euler_tendsto (twist_norm_le hf χ t) hσ).norm
  have h2 := (realPower_euler_tendsto hσ).mul_const
    (Real.exp (1-Real.exp (-1)*distanceSq f χ t N))
  simp only [complete_twist,twist] at h1
  apply le_of_tendsto_of_tendsto h1 h2
  filter_upwards [eventually_gt_atTop N] with K hK
  have hnorm := unnormalized_product_norm_le K.primesBelow
    (fun p => (p:ℝ)^(-σ)) (twist f χ t)
    (fun p hp => Real.rpow_nonneg (Nat.cast_nonneg p) _)
    (fun p hp => prime_weight_half hσ.le (Nat.mem_primesBelow.mp hp).2)
    (fun p hp => twist_norm_le hf χ t p)
  refine hnorm.trans ?_
  apply mul_le_mul_of_nonneg_left
  · apply Real.exp_le_exp.mpr
    have hd := weighted_distance_lower hf χ t hN hK hσN
    have hs := prime_weight_squares_le hσ.le (show 1≤K by omega)
    linarith
  · apply prod_nonneg
    intro p hp
    apply inv_nonneg.mpr
    have he := prime_weight_half hσ.le (Nat.mem_primesBelow.mp hp).2
    linarith

theorem compact_vertical_saving {f : ℕ → ℂ} (hf : OneBounded f)
    (hNP : UniformlyNonpretentious f) {q : ℕ} (hq : 0<q)
    (χ : DirichletCharacter ℂ q) (T : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∃ η : ℝ, 0<η ∧ ∀ δ : ℝ, 0<δ → δ≤η → ∀ t : ℝ, |t|≤T →
      ‖verticalSeries f χ (1+δ) t‖ ≤ ε*(∑' n : ℕ, (n:ℝ)^(-(1+δ))) := by
  obtain ⟨N,hd,hN2,hNT⟩ := ((eventual_distanceSq_lower hf hNP q hq χ
    ((1-Real.log ε)/Real.exp (-1))).and
    ((eventually_ge_atTop (2:ℕ)).and
    (eventually_ge_atTop ⌈T⌉₊))).exists
  have hl : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  refine ⟨1/Real.log N,one_div_pos.mpr hl,?_⟩
  intro δ hδ hδη t ht
  have htN : t ∈ Set.Icc (-(N:ℝ)) (N:ℝ) := by
    have hTN : T≤N := (Nat.le_ceil T).trans (by exact_mod_cast hNT)
    exact abs_le.mp (ht.trans hTN)
  have he : Real.exp (1-Real.exp (-1)*distanceSq f χ t N) ≤ ε := by
    rw [←Real.exp_log hε]
    apply Real.exp_le_exp.mpr
    have hh := (div_le_iff₀ (Real.exp_pos (-1))).mp (hd t htN)
    linarith
  calc
    _ ≤ _ := vertical_series_norm_le hf χ t hN2 (by linarith) (by linarith)
    _ ≤ _ := by
      rw [mul_comm ε]
      exact mul_le_mul_of_nonneg_left he (tsum_nonneg (fun n =>
        Real.rpow_nonneg (Nat.cast_nonneg n) _))

end OrdinaryCorrelations.PretentiousEuler

end

end OAI
