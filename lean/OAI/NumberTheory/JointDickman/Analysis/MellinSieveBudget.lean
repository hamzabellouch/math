import OAI.NumberTheory.JointDickman.Analysis.MellinPrimeSamplingArithmetic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! # Elementary budgets for sparse prime sampling -/
namespace JointDickman
open Filter Finset
open scoped Topology

lemma prime_survival_eventually_le : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ x : ℝ in atTop,
      (∏ p ∈ (Icc 2 ⌊x⌋₊).filter Nat.Prime, (1-1/(p:ℝ))) ≤ C/Real.log x := by
  let C := Real.exp (-Real.eulerMascheroniConstant)+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  have hh := primeProductMertensInput.eventually
    (eventually_lt_nhds (lt_add_one (Real.exp (-Real.eulerMascheroniConstant))))
  filter_upwards [hh, eventually_gt_atTop (1:ℝ)] with x hx hx1
  rw [le_div_iff₀ (Real.log_pos hx1)]
  simpa only [mul_comm] using hx.le

lemma logarithmic_power_decay (k : ℕ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => (Real.log x)^k*x^(-a)) atTop (𝓝 0) := by
  have hh := (isLittleO_log_rpow_rpow_atTop (k:ℝ) ha).tendsto_div_nhds_zero
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  rw [Real.rpow_natCast, Real.rpow_neg hx.le, div_eq_mul_inv]

noncomputable def mellinSparseBudget (A δ κ q : ℝ) : ℝ :=
  132*q^(2*κ-1)*Real.log q + 176*A*q^(2*κ-10*δ)*(Real.log q)^2

lemma mellinSparseBudget_tendsto (A : ℝ) {δ κ : ℝ} (hδ : 0 < δ)
    (hκ : κ ≤ 1/8) (hκδ : κ ≤ δ) :
    Tendsto (mellinSparseBudget A δ κ) atTop (𝓝 0) := by
  have h1 : 0 < 1-2*κ := by linarith
  have h2 : 0 < 10*δ-2*κ := by linarith
  have ha := (logarithmic_power_decay 1 h1).const_mul 132
  have hb := (logarithmic_power_decay 2 h2).const_mul (176*A)
  have hh := ha.add hb
  simp only [mul_zero, add_zero] at hh
  apply hh.congr
  intro q
  dsimp [mellinSparseBudget]
  rw [show -(1-2*κ) = 2*κ-1 by ring, show -(10*δ-2*κ) = 2*κ-10*δ by ring]
  ring

lemma mellin_dyadic_count_le {q : ℕ} (hq : 2 ≤ q) :
    ((Nat.log 2 (q^3)+1:ℕ):ℝ) ≤ 8*Real.log q := by
  have hqR : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0:ℝ) < q := by linarith
  have hlog2 : (1/2:ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hlog : (1/2:ℝ) ≤ Real.log q := hlog2.trans
    (Real.log_le_log (by norm_num) hqR)
  have hh := dyadic_block_count_le (q^3)
  rw [Nat.cast_pow, Real.log_pow] at hh
  have hd : Real.log ((q:ℝ)) * 3 / Real.log 2 ≤ 6*Real.log q := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr
    nlinarith
  have hd' : 3*Real.log (q:ℝ)/Real.log 2 ≤ 6*Real.log q := by simpa only [mul_comm] using hd
  norm_num only [Nat.cast_ofNat] at hh
  linarith

lemma mellin_sieve_remainder_ratio {q N A δ κ z s j : ℝ}
    (hq : 2 ≤ q) (hA : 0 ≤ A) (hδ : 0 < δ)
    (hNlo : q^10 ≤ N) (hNhi : N ≤ q^11)
    (_hz : 0 ≤ z) (hzq : z ≤ 2*q^κ) (hs : 0 ≤ s) (hsq : s ≤ q^κ)
    (hj : 0 ≤ j) (hjq : j ≤ 8*Real.log q) :
    z*(6*q^9+j*A*N^(1-δ))*s/N*Real.log N ≤ mellinSparseBudget A δ κ q := by
  have hq0 : 0 < q := by linarith
  have hN : 0 < N := (pow_pos hq0 10).trans_le hNlo
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg ((one_le_pow₀ (by linarith : 1 ≤ q)).trans hNlo)
  have hl : Real.log N ≤ 11*Real.log q := by
    have hh := Real.log_le_log hN hNhi
    rwa [Real.log_pow] at hh
  have hf : q^9/N ≤ q^(-1:ℝ) := by
    calc
      _ ≤ q^9/q^10 := div_le_div_of_nonneg_left (by positivity) (by positivity) hNlo
      _ = _ := by rw [← Real.rpow_natCast q 9, ← Real.rpow_natCast q 10, ← Real.rpow_sub hq0]; norm_num
  have hn : N^(1-δ)/N ≤ q^(-10*δ) := by
    have he : N^(1-δ)/N = N^(-δ) := by
      calc
        _ = N^(1-δ)/N^(1:ℝ) := by rw [Real.rpow_one]
        _ = N^((1-δ)-1) := (Real.rpow_sub hN _ _).symm
        _ = _ := by congr 1; ring
    rw [he]
    apply (Real.rpow_le_rpow_of_nonpos (pow_pos hq0 10) hNlo (by linarith)).trans_eq
    rw [← Real.rpow_natCast q 10, ← Real.rpow_mul hq0.le]
    congr 1
    ring
  have he : (6*q^9+j*A*N^(1-δ))/N ≤ 6*q^(-1:ℝ)+8*Real.log q*A*q^(-10*δ) := by
    calc
      _ = 6*(q^9/N)+(j*A)*(N^(1-δ)/N) := by ring
      _ ≤ 6*q^(-1:ℝ)+(8*Real.log q*A)*q^(-10*δ) := by
        apply add_le_add (mul_le_mul_of_nonneg_left hf (by norm_num))
        exact mul_le_mul (mul_le_mul_of_nonneg_right hjq hA) hn
          (by positivity) (by positivity)
      _ = _ := by ring
  have hzs : z*s ≤ 2*q^(2*κ) := by
    calc
      _ ≤ (2*q^κ)*q^κ := mul_le_mul hzq hsq hs (by positivity)
      _ = _ := by rw [mul_assoc, ← Real.rpow_add hq0]; congr 2; ring
  have hE : 0 ≤ (6*q^9+j*A*N^(1-δ))/N := by positivity
  have hp1 : q^(2*κ)*q^(-1:ℝ) = q^(2*κ-1) := by rw [← Real.rpow_add hq0]; congr 1
  have hp2 : q^(2*κ)*q^(-10*δ) = q^(2*κ-10*δ) := by rw [← Real.rpow_add hq0]; congr 1; ring
  calc
    _ = (z*s)*((6*q^9+j*A*N^(1-δ))/N)*Real.log N := by ring
    _ ≤ (2*q^(2*κ))*(6*q^(-1:ℝ)+8*Real.log q*A*q^(-10*δ))*(11*Real.log q) :=
      mul_le_mul (mul_le_mul hzs he hE (by positivity)) hl hlogN (by positivity)
    _ = 132*(q^(2*κ)*q^(-1:ℝ))*Real.log q+
        176*A*(q^(2*κ)*q^(-10*δ))*(Real.log q)^2 := by ring
    _ = _ := by rw [hp1,hp2]; rfl

/-- The complete remainder is smaller than the prime-density scale for
sufficiently sparse samples and a correspondingly small sieve level. -/
theorem mellin_sieve_remainder_absorption (A : ℝ) (hA : 0 ≤ A)
    {δ κ : ℝ} (hδ : 0 < δ) (hκ : κ ≤ 1/8) (hκδ : κ ≤ δ) :
    ∀ᶠ q : ℝ in atTop, ∀ N z s j : ℝ,
      q^10 ≤ N → N ≤ q^11 →
      0 ≤ z → z ≤ 2*q^κ → 0 ≤ s → s ≤ q^κ →
      0 ≤ j → j ≤ 8*Real.log q →
      z*(6*q^9+j*A*N^(1-δ))*s ≤ N/Real.log N := by
  have hlim := mellinSparseBudget_tendsto A hδ hκ hκδ
  filter_upwards [eventually_ge_atTop (2:ℝ), hlim.eventually (eventually_lt_nhds zero_lt_one)] with q hq hb
  intro N z s j hNlo hNhi hz hzq hs hsq hj hjq
  have hN1 : 1 < N := (one_lt_pow₀ (by linarith : 1 < q) (by norm_num : 10 ≠ 0)).trans_le hNlo
  have hratio := (mellin_sieve_remainder_ratio hq hA hδ hNlo hNhi hz hzq hs hsq hj hjq).trans hb.le
  apply (le_div_iff₀ (Real.log_pos hN1)).mpr
  apply (div_le_one (by linarith : 0 < N)).mp
  convert hratio using 1; ring

end JointDickman

end OAI
