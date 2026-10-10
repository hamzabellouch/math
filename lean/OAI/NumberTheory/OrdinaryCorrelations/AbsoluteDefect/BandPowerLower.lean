import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ModOneCharacter

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

namespace OrdinaryCorrelations.PretentiousEuler
open Finset Completion NonpretentiousEuler

lemma band_power_lower {N p : ℕ} (hN : 2≤N) (hp : 0<p) (hpN : p≤N)
    {A u : ℝ} (hA : 0≤A) (hu : u≤A/Real.log N) :
    Real.exp (-A)/(p:ℝ) ≤ (p:ℝ)^(-(1+u)) := by
  have hp0 : (0:ℝ)<p := by exact_mod_cast hp
  have hl : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hp1 : (1:ℝ)≤p := by exact_mod_cast hp
  have hlp : 0≤Real.log p := Real.log_nonneg hp1
  have hlpN : Real.log p≤Real.log N := Real.log_le_log hp0 (by exact_mod_cast hpN)
  have hm : u*Real.log p≤A := by
    calc
      _ ≤ (A/Real.log N)*Real.log p := mul_le_mul_of_nonneg_right hu hlp
      _ ≤ (A/Real.log N)*Real.log N := mul_le_mul_of_nonneg_left hlpN (div_nonneg hA hl.le)
      _ = A := div_mul_cancel₀ _ hl.ne'
  calc
    _ = Real.exp (-A-Real.log p) := by rw [Real.exp_sub,Real.exp_log hp0]
    _ ≤ Real.exp (Real.log p*(-(1+u))) := by apply Real.exp_le_exp.mpr; nlinarith
    _ = _ := (Real.rpow_def_of_pos hp0 _).symm

lemma band_distance_lower {f : ℕ → ℂ} (hf : OneBounded f) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) {N K : ℕ} (hN : 2≤N) (hK : N<K)
    {A u : ℝ} (hA : 0≤A) (hu : u≤A/Real.log N) :
    Real.exp (-A)*distanceSq f χ t N ≤
      ∑p∈K.primesBelow, (p:ℝ)^(-(1+u))*(1-(twist f χ t p).re) := by
  let P := (Finset.Icc 2 N).filter Nat.Prime
  have hsub : P ⊆ K.primesBelow := by
    intro p hp
    obtain ⟨hpI,hpp⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp2,hpN⟩ := Finset.mem_Icc.mp hpI
    exact Nat.mem_primesBelow.mpr ⟨lt_of_le_of_lt hpN hK,hpp⟩
  have hre (p : ℕ) : 0≤1-(twist f χ t p).re := by
    have hh := (Complex.re_le_norm (twist f χ t p)).trans (twist_norm_le hf χ t p)
    linarith
  calc
    _ = ∑p∈P, (Real.exp (-A)/(p:ℝ))*(1-(twist f χ t p).re) := by
      simp only [distanceSq,Nat.floor_natCast,mul_sum]
      apply sum_congr rfl
      intro p hp
      change Real.exp (-A)*((1-(twist f χ t p).re)/(p:ℝ))=_
      ring
    _ ≤ ∑p∈P, (p:ℝ)^(-(1+u))*(1-(twist f χ t p).re) := by
      apply sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_right (band_power_lower hN (Finset.mem_filter.mp hp).2.pos
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2 hA hu) (hre p)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ =>
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _) (hre p))

theorem band_vertical_norm_le {f : ℕ → ℂ} (hf : OneBounded f) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) {N : ℕ} (hN : 2≤N)
    {A u : ℝ} (hA : 0≤A) (hu : 0<u) (huN : u≤A/Real.log N) :
    ‖verticalSeries f χ (1+u) t‖ ≤ (∑' n : ℕ, (n:ℝ)^(-(1+u))) *
      Real.exp (1-Real.exp (-A)*distanceSq f χ t N) := by
  have hu1 : 1<1+u := by linarith
  have h1 := (weighted_euler_tendsto (twist_norm_le hf χ t) hu1).norm
  have h2 := (realPower_euler_tendsto hu1).mul_const
    (Real.exp (1-Real.exp (-A)*distanceSq f χ t N))
  simp only [complete_twist,twist] at h1
  apply le_of_tendsto_of_tendsto h1 h2
  filter_upwards [eventually_gt_atTop N] with K hK
  have hnorm := unnormalized_product_norm_le K.primesBelow
    (fun p => (p:ℝ)^(-(1+u))) (twist f χ t)
    (fun p hp => Real.rpow_nonneg (Nat.cast_nonneg p) _)
    (fun p hp => prime_weight_half hu1.le (Nat.mem_primesBelow.mp hp).2)
    (fun p hp => twist_norm_le hf χ t p)
  refine hnorm.trans ?_
  apply mul_le_mul_of_nonneg_left
  · apply Real.exp_le_exp.mpr
    have hd := band_distance_lower hf χ t hN hK hA huN
    have hs := prime_weight_squares_le hu1.le (show 1≤K by omega)
    linarith
  · apply prod_nonneg
    intro p hp
    apply inv_nonneg.mpr
    have he := prime_weight_half hu1.le (Nat.mem_primesBelow.mp hp).2
    linarith

theorem eventual_band_saving {f : ℕ → ℂ} (hf : OneBounded f)
    (hNP : UniformlyNonpretentious f) {A ε : ℝ} (hA : 0≤A) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀u : ℝ, 0<u → u≤2 → u≤A/Real.log N →
      ∀t : ℝ, |t|≤N →
      ‖LSeries (complete f) ((1+u:ℝ)+(t:ℂ)*Complex.I)‖≤ε/u := by
  have he3 : 0<ε/3 := by positivity
  filter_upwards [eventual_distanceSq_lower hf hNP 1 (by norm_num)
    (1 : DirichletCharacter ℂ 1) ((1-Real.log (ε/3))/Real.exp (-A)),
    eventually_ge_atTop (2:ℕ)] with N hdist hN
  intro u hu hu2 huN t ht
  have he : Real.exp (1-Real.exp (-A)*distanceSq f (1 : DirichletCharacter ℂ 1) t N)≤ε/3 := by
    rw [←Real.exp_log he3]
    apply Real.exp_le_exp.mpr
    have hh := (div_le_iff₀ (Real.exp_pos (-A))).mp (hdist t (abs_le.mp ht))
    linarith
  rw [LSeries_complete_eq]
  calc
    _ ≤ _ := band_vertical_norm_le hf (1 : DirichletCharacter ℂ 1) t hN hA hu huN
    _ ≤ (∑' n : ℕ, (n:ℝ)^(-(1+u)))*(ε/3) := mul_le_mul_of_nonneg_left he
      (tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _))
    _ ≤ (1+1/u)*(ε/3) := mul_le_mul_of_nonneg_right
      (OrdinaryPowerBounds.power_sum_le hu) he3.le
    _ ≤ ε/u := by
      have hh : (1+1/u)*u=1+u := by field_simp; ring
      apply (le_div_iff₀ hu).mpr
      nlinarith

end OrdinaryCorrelations.PretentiousEuler

end

end OAI
