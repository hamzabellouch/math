import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.OneBounded
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.OneOrZero
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.NormOneAddLeExp

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

def realPowerHom (σ : ℝ) (hσ : σ ≠ 0) : ℕ →*₀ ℝ where
  toFun n := (n:ℝ)^(-σ)
  map_zero' := by simp [hσ]
  map_one' := by simp
  map_mul' m n := by simp [Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

def weightedHom (z : ℕ → ℂ) (σ : ℝ) (hσ : σ ≠ 0) : ℕ →*₀ ℂ where
  toFun n := complete z n * (↑((n:ℝ)^(-σ)):ℂ)
  map_zero' := by
    rw [Nat.cast_zero, Real.zero_rpow (neg_ne_zero.mpr hσ), Complex.ofReal_zero, mul_zero]
  map_one' := by simp
  map_mul' m n := by
    simp only [complete_mul,Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n),
      Complex.ofReal_mul]
    ring

lemma weightedHom_norm_summable {z : ℕ → ℂ} (hz : OneBounded z) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n => ‖weightedHom z σ (by linarith) n‖) := by
  have hsum : Summable (fun n : ℕ => (n:ℝ)^(-σ)) := Real.summable_nat_rpow.mpr (by linarith)
  apply hsum.of_nonneg_of_le (fun n => norm_nonneg _)
  intro n
  change ‖complete z n * (↑((n:ℝ)^(-σ)):ℂ)‖ ≤ _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg n) _) (complete_oneBounded hz n)

lemma realPowerHom_norm_summable {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n => ‖realPowerHom σ (by linarith) n‖) := by
  simpa only [realPowerHom,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk,
    Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] using
    (Real.summable_nat_rpow.mpr (show -σ < -1 by linarith))

lemma negativePower_le_inv {σ : ℝ} (hσ : 1 ≤ σ) {p : ℕ} (hp : Nat.Prime p) :
    (p:ℝ)^(-σ) ≤ (p:ℝ)⁻¹ := by
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  simpa only [Real.rpow_neg_one] using Real.rpow_le_rpow_of_exponent_le hp1 (show -σ ≤ (-1:ℝ) by linarith)

lemma prime_weight_half {σ : ℝ} (hσ : 1 ≤ σ) {p : ℕ} (hp : Nat.Prime p) :
    (p:ℝ)^(-σ) ≤ 1/2 := by
  refine (negativePower_le_inv hσ hp).trans ?_
  simpa using inv_anti₀ (by norm_num : (0:ℝ)<2) (show (2:ℝ) ≤ p by exact_mod_cast hp.two_le)

lemma prime_weight_squares_le {σ : ℝ} (hσ : 1 ≤ σ) {K : ℕ} (hK : 1 ≤ K) :
    ∑ p ∈ K.primesBelow, ((p:ℝ)^(-σ))^2 ≤ 1 := by
  have hsub : K.primesBelow ⊆ (Icc 2 K).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpK,hp⟩ := Nat.mem_primesBelow.mp hp
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.two_le,hpK.le⟩,hp⟩
  calc
    _ ≤ ∑ p ∈ K.primesBelow, (p:ℝ)⁻¹^2 := by
      apply sum_le_sum
      intro p hp
      have he := negativePower_le_inv hσ (Nat.mem_primesBelow.mp hp).2
      have hn := Real.rpow_nonneg (Nat.cast_nonneg p) (-σ)
      nlinarith
    _ ≤ ∑ p ∈ (Icc 2 K).filter Nat.Prime, (p:ℝ)⁻¹^2 :=
      sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => sq_nonneg _)
    _ ≤ 1 := prime_inv_sq_sum_le hK

lemma cutoff_negativePower_lower {N : ℕ} (hN : 2 ≤ N) {p : ℕ}
    (hp : 0 < p) (hpN : p ≤ N) :
    Real.exp (-1) / (p:ℝ) ≤ (p:ℝ)^(-(1+1/Real.log N)) := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp
  have hN1 : (1:ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos hN1
  have hlogp : Real.log p ≤ Real.log N := Real.log_le_log hp0 (by exact_mod_cast hpN)
  have hratio : Real.log p / Real.log N ≤ 1 := (div_le_one hlog).mpr hlogp
  calc
    _ = Real.exp (-1-Real.log p) := by rw [Real.exp_sub,Real.exp_log hp0]
    _ ≤ Real.exp (Real.log p * (-(1+1/Real.log N))) := by
      apply Real.exp_le_exp.mpr
      have hid : Real.log p * (-(1+1/Real.log N)) = -Real.log p - Real.log p/Real.log N := by ring
      rw [hid]
      linarith
    _ = _ := (Real.rpow_def_of_pos hp0 _).symm

lemma realPower_euler_tendsto {σ : ℝ} (hσ : 1 < σ) :
    Tendsto (fun K : ℕ => ∏ p ∈ K.primesBelow, (1-(p:ℝ)^(-σ))⁻¹)
      atTop (nhds (∑' n : ℕ, (n:ℝ)^(-σ))) := by
  simpa only [realPowerHom,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk] using
    (EulerProduct.eulerProduct_completely_multiplicative (realPowerHom_norm_summable hσ))

lemma weighted_euler_tendsto {z : ℕ → ℂ} (hz : OneBounded z) {σ : ℝ} (hσ : 1 < σ) :
    Tendsto (fun K : ℕ => ∏ p ∈ K.primesBelow, (1-(↑((p:ℝ)^(-σ)):ℂ)*z p)⁻¹)
      atTop (nhds (∑' n : ℕ, complete z n * (↑((n:ℝ)^(-σ)):ℂ))) := by
  have hh := EulerProduct.eulerProduct_completely_multiplicative (weightedHom_norm_summable hz hσ)
  convert hh using 1
  · ext K
    apply prod_congr rfl
    intro p hp
    simp only [weightedHom,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk,
      complete_prime z (Nat.mem_primesBelow.mp hp).2]
    rw [mul_comm]
  · rfl

end OrdinaryCorrelations.PretentiousEuler

end

end OAI
