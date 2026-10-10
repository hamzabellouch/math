import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.TriangleMain

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace OrdinaryLogIntegral
open Finset

theorem divisorTriangle_high_at_scale (t : ℝ) (u B d : ℕ) (hu : 1 ≤ u)
    (hB : 0 < B) (hBU : B ≤ u^8) (hd : 0 < d) (hdB : d ≤ B)
    (htlo : (u : ℝ)^7 ≤ |t|) (hthi : |t| ≤ (u : ℝ)^10) :
    ‖divisorTriangle t B d‖ ≤ 1500*(u : ℝ)^7 := by
  have hu0 : 0 < u := by omega
  have hu' : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hb : 0 < (B/d : ℕ) := Nat.div_pos hdB hd
  obtain ⟨haU,hNU,hNa,hNd⟩ := divisor_parameters B d hB hd hdB
  have ht : t ≠ 0 := by
    intro h
    have hp : (0 : ℝ) < (u : ℝ)^7 := by positivity
    simp [h] at htlo
    linarith
  have hh := divisorTriangle_high t B d (u^4) hB hd hdB ht (pow_pos hu0 _)
  have hbud := power_budget_bound t (B/d : ℕ) u (6*B/d+1-B/d) (u^4) hu'
    (by exact_mod_cast hb) (by exact_mod_cast haU.trans hBU)
    (by exact_mod_cast hNU.trans (Nat.mul_le_mul_left 7 hBU))
    (by exact_mod_cast hNa) (by norm_cast) htlo hthi (prime_harmonic_power_bound u hu)
  have hk : (0 : ℝ) < (u^4 : ℕ) := by positivity
  have hroot : Real.sqrt (differencingBudget t (B/d : ℕ) (6*B/d+1-B/d) (u^4)) /
      (u^4 : ℕ) ≤ 300*(u : ℝ)^7 := by
    apply (div_le_iff₀ hk).mpr
    apply (Real.sqrt_le_left (by positivity)).mpr
    have hh := (div_le_iff₀ (sq_pos_of_pos hk)).mp hbud
    nlinarith only [hh]
  have hfac : 1+((6*B/d+1-B/d : ℕ) : ℝ)*d/(2*(B : ℕ)) ≤ 5 := by
    have hn : ((6*B/d+1-B/d : ℕ) : ℝ)*d ≤ 7*B := by exact_mod_cast hNd
    have hb' : (0 : ℝ) < B := by exact_mod_cast hB
    have hh : ((6*B/d+1-B/d : ℕ) : ℝ)*d/(2*(B : ℕ)) ≤ 4 := by
      apply (div_le_iff₀ (show (0 : ℝ) < 2*(B : ℕ) by positivity)).mpr
      linarith
    linarith
  calc
    _ ≤ _ := hh
    _ ≤ 5*(300*(u : ℝ)^7) := mul_le_mul hfac hroot (by positivity) (by norm_num)
    _ = _ := by ring

lemma divisorTriangle_low_at_scale (t : ℝ) (u B d : ℕ) (hu : 1 ≤ u)
    (hB : 0 < B) (hd : 0 < d) (hdB : d ≤ B) (ht : |t| ≤ (u : ℝ)^7) :
    ‖divisorTriangle t B d - ((d : ℝ)⁻¹ : ℝ) • triangleMain t B‖ ≤ 11*(u : ℝ)^7 := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have hh := divisorTriangle_low_error t B d hB hd
  rw [divisorTriangle_main_eq] at hh
  have hN : ((6*B/d+1 : ℕ) : ℝ)*d ≤ 7*B := by
    have hg := Nat.div_mul_le_self (6*B) d
    have hh : (6*B/d+1)*d ≤ 7*B := by nlinarith
    exact_mod_cast hh
  have hU : (1 : ℝ) ≤ (u : ℝ)^7 := one_le_pow₀ (by exact_mod_cast hu)
  calc
    _ ≤ _ := hh
    _ ≤ 7*B*((2*(B : ℝ))⁻¹+|t|/B) := by gcongr
    _ = 7/2+7*|t| := by field_simp
    _ ≤ _ := by linarith

theorem divisorTriangle_uniform_at_scale (t : ℝ) (u B d : ℕ) (hu : 1 ≤ u)
    (hB : 0 < B) (hBU : B ≤ u^8) (hd : 0 < d) (hdB : d ≤ B)
    (ht : |t| ≤ (u : ℝ)^10) :
    ‖divisorTriangle t B d - ((d : ℝ)⁻¹ : ℝ) • triangleMain t B‖ ≤ 1600*(u : ℝ)^7 := by
  have hu0 : 0 < u := by omega
  have hu' : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hBUr : (B:ℝ) ≤ (u:ℝ)^8 := by exact_mod_cast hBU
  by_cases hlo : |t| ≤ (u : ℝ)^7
  · exact (divisorTriangle_low_at_scale t u B d hu hB hd hdB hlo).trans (by gcongr; norm_num)
  have hhi : (u : ℝ)^7 ≤ |t| := le_of_lt (lt_of_not_ge hlo)
  have hdisc := divisorTriangle_high_at_scale t u B d hu hB hBU hd hdB hhi ht
  have hmain := triangleMain_bound t B hB
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have ht' : (u : ℝ)^7 ≤ 1+t^2 := by
    have ha : 1 ≤ |t| := (one_le_pow₀ hu' : 1 ≤ (u:ℝ)^7).trans hhi
    nlinarith [sq_abs t]
  have hsm : ‖((d : ℝ)⁻¹ : ℝ) • triangleMain t B‖ ≤ 22*(u : ℝ)^7 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (d : ℝ)⁻¹)]
    calc
      _ ≤ 1 * (22*(B:ℝ)/(1+t^2)) := by
        gcongr
        exact inv_le_one_of_one_le₀ hd'
      _ ≤ 22*(u : ℝ)^8/(u : ℝ)^7 := by
        simp only [one_mul]
        gcongr
      _ = 22*(u : ℝ) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa using pow_le_pow_right₀ hu' (show 1 ≤ 7 by norm_num)) (by norm_num)
  calc
    _ ≤ ‖divisorTriangle t B d‖ + ‖((d : ℝ)⁻¹ : ℝ) • triangleMain t B‖ := norm_sub_le _ _
    _ ≤ 1500*(u : ℝ)^7+22*(u : ℝ)^7 := add_le_add hdisc hsm
    _ ≤ _ := by nlinarith [pow_nonneg (Nat.cast_nonneg u : (0 : ℝ) ≤ u) 7]

end OrdinaryLogIntegral

end

end OAI
