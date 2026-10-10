import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SumMultiples

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset

namespace OrdinaryLogIntegral
open Finset

lemma prime_harmonic_power_bound (u : ℕ) (hu : 1 ≤ u) :
    (∑ d ∈ Icc 1 (u^4), (d : ℝ)⁻¹) ≤ 5*(u : ℝ) := by
  have hh := harmonic_le_one_add_log (u^4)
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
    Nat.cast_pow, Real.log_pow] at hh
  have hu' : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hl := Real.log_le_sub_one_of_pos (show (0 : ℝ) < u by linarith)
  norm_num at hh
  linarith

lemma differencingBudget_div_sq (t a : ℝ) (N K : ℕ) (ht : t ≠ 0) (ha : a ≠ 0) (hK : K ≠ 0) :
    differencingBudget t a N K / (K : ℝ)^2 =
      2*(N : ℝ)^2/K + 28*N*(a+N+K)^2*(∑ d ∈ Icc 1 K, (d : ℝ)⁻¹)/(K*|t|) +
      4*(N : ℝ)^2*|t| *K/a^2 + 8*(K : ℝ)^2 := by
  unfold differencingBudget
  have hk : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hK
  have htt : |t| ≠ 0 := abs_ne_zero.mpr ht
  field_simp
  ring

lemma power_budget_bound (t a U : ℝ) (N K : ℕ) (hU : 1 ≤ U) (ha : 0 < a)
    (haU : a ≤ U^8) (hNU : (N : ℝ) ≤ 7*U^8) (hNa : (N : ℝ) ≤ 12*a)
    (hK : (K : ℝ) = U^4) (htlo : U^7 ≤ |t|) (hthi : |t| ≤ U^10)
    (hH : (∑ d ∈ Icc 1 K, (d : ℝ)⁻¹) ≤ 5*U) :
    differencingBudget t a N K / (K : ℝ)^2 ≤ 90000*U^14 := by
  have hU0 : 0 < U := by linarith
  have hk : (0 : ℝ) < K := by rw [hK]; positivity
  have hkn : K ≠ 0 := by exact_mod_cast ne_of_gt hk
  have ht : t ≠ 0 := by
    intro h
    have hp : (0 : ℝ) < U^7 := by positivity
    simp [h] at htlo
    linarith
  rw [differencingBudget_div_sq t a N K ht (ne_of_gt ha) hkn]
  have hKle : (K : ℝ) ≤ U^8 := by rw [hK]; exact pow_le_pow_right₀ hU (by norm_num)
  have hs : a+N+K ≤ 9*U^8 := by linarith
  have h1 : 2*(N : ℝ)^2/K ≤ 98*U^14 := by
    calc
      _ ≤ 2*(7*U^8)^2/U^4 := by rw [hK]; gcongr
      _ = 98*U^12 := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hU (show 12 ≤ 14 by norm_num)) (by norm_num)
  have h2 : 28*N*(a+N+K)^2*(∑ d ∈ Icc 1 K, (d : ℝ)⁻¹)/(K*|t|) ≤ 79380*U^14 := by
    calc
      _ ≤ 28*(7*U^8)*(9*U^8)^2*(5*U)/(U^4*U^7) := by
        rw [hK]
        rw [hK] at hs
        gcongr
      _ = _ := by field_simp; ring
  have hratio : (N : ℝ)^2/a^2 ≤ 144 := by
    apply (div_le_iff₀ (sq_pos_of_pos ha)).mpr
    nlinarith [sq_le_sq₀ (Nat.cast_nonneg N) (by positivity : 0 ≤ 12*a) |>.mpr hNa]
  have h3 : 4*(N : ℝ)^2*|t| *K/a^2 ≤ 576*U^14 := by
    calc
      _ = 4*((N : ℝ)^2/a^2)*|t| *(K : ℝ) := by ring
      _ ≤ 4*144*U^10*U^4 := by rw [hK]; gcongr
      _ = _ := by ring
  have h4 : 8*(K : ℝ)^2 ≤ 8*U^14 := by
    rw [hK]
    calc
      8*(U^4)^2 = 8*U^8 := by ring
      _ ≤ 8*U^14 := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hU (show 8 ≤ 14 by norm_num)) (by norm_num)
  nlinarith [pow_nonneg hU0.le 14]

lemma divisor_parameters (B d : ℕ) (_hB : 0 < B) (hd : 0 < d) (hdB : d ≤ B) :
    (B/d : ℕ) ≤ B ∧ (6*B/d+1-B/d : ℕ) ≤ 7*B ∧
    (6*B/d+1-B/d : ℕ) ≤ 12*(B/d) ∧
    (6*B/d+1-B/d : ℕ)*d ≤ 7*B := by
  have hb : 1 ≤ B/d := Nat.div_pos hdB hd
  have hbB : B/d ≤ B := Nat.div_le_self _ _
  have hq := Nat.div_mul_le_self (6*B) d
  have hqB := Nat.div_le_self (6*B) d
  have hr := Nat.lt_mul_div_succ B hd
  have hc : 6*B/d+1 ≤ 6*(B/d)+6 := by
    have hq' : (6*B/d)*d ≤ 6*B := by simpa only [mul_comm] using hq
    have hcontra : 6*B/d < 6*(B/d+1) := by
      by_contra hn
      have hh := Nat.mul_le_mul_right d (le_of_not_gt hn)
      nlinarith
    omega
  refine ⟨hbB, ?_, ?_, ?_⟩
  · omega
  · omega
  · have hh : (6*B/d+1-B/d)*d ≤ (6*B/d+1)*d :=
      Nat.mul_le_mul_right d (Nat.sub_le _ _)
    nlinarith

theorem divisorTriangle_high_power (t : ℝ) (u d : ℕ) (hu : 1 ≤ u) (hd : 0 < d)
    (hdB : d ≤ u^8) (htlo : (u : ℝ)^7 ≤ |t|) (hthi : |t| ≤ (u : ℝ)^10) :
    ‖divisorTriangle t (u^8) d‖ ≤ 1500*(u : ℝ)^7 := by
  have hu0 : 0 < u := by omega
  have hu' : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hB : 0 < u^8 := pow_pos hu0 _
  have hb : 0 < (u^8/d : ℕ) := Nat.div_pos hdB hd
  obtain ⟨haU,hNU,hNa,hNd⟩ := divisor_parameters (u^8) d hB hd hdB
  have ht : t ≠ 0 := by
    intro h
    have hp : (0 : ℝ) < (u : ℝ)^7 := by positivity
    simp [h] at htlo
    linarith
  have hh := divisorTriangle_high t (u^8) d (u^4) hB hd hdB ht (pow_pos hu0 _)
  have hbud := power_budget_bound t (u^8/d : ℕ) u (6*u^8/d+1-u^8/d) (u^4) hu'
    (by exact_mod_cast hb) (by exact_mod_cast haU) (by exact_mod_cast hNU)
    (by exact_mod_cast hNa) (by norm_cast) htlo hthi (prime_harmonic_power_bound u hu)
  have hk : (0 : ℝ) < (u^4 : ℕ) := by positivity
  have hroot : Real.sqrt (differencingBudget t (u^8/d : ℕ) (6*u^8/d+1-u^8/d) (u^4)) /
      (u^4 : ℕ) ≤ 300*(u : ℝ)^7 := by
    apply (div_le_iff₀ hk).mpr
    apply (Real.sqrt_le_left (by positivity)).mpr
    have hh := (div_le_iff₀ (sq_pos_of_pos hk)).mp hbud
    nlinarith only [hh]
  have hfac : 1+((6*u^8/d+1-u^8/d : ℕ) : ℝ)*d/(2*(u^8 : ℕ)) ≤ 5 := by
    have hn : ((6*u^8/d+1-u^8/d : ℕ) : ℝ)*d ≤ 7*(u^8 : ℕ) := by exact_mod_cast hNd
    have hb' : (0 : ℝ) < (u^8 : ℕ) := by positivity
    have hh : ((6*u^8/d+1-u^8/d : ℕ) : ℝ)*d/(2*(u^8 : ℕ)) ≤ 4 := by
      apply (div_le_iff₀ (show (0 : ℝ) < 2*(u^8 : ℕ) by positivity)).mpr
      linarith
    linarith
  calc
    _ ≤ _ := hh
    _ ≤ 5*(300*(u : ℝ)^7) := mul_le_mul hfac hroot (by positivity) (by norm_num)
    _ = _ := by ring

end OrdinaryLogIntegral

end

end OAI
