import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrimeHarmonicPowerBound

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset

namespace OrdinaryLogIntegral
open Finset

noncomputable def triangleMain (t : ℝ) (B : ℕ) : ℂ :=
  ((2*(B : ℝ))⁻¹ : ℝ) • triangleMellin t B (2*B)

lemma triangleMain_bound (t : ℝ) (B : ℕ) (hB : 0 < B) :
    ‖triangleMain t B‖ ≤ 22*B/(1+t^2) := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have hh := triangleMellin_bound t B (2*B) hb (by positivity)
  have hp : 0 < 1+t^2 := by positivity
  have hl : ‖triangleMellin t B (2*B)‖ ≤ 44*(B : ℝ)^2/(1+t^2) := by
    apply (le_div_iff₀ hp).mpr
    nlinarith only [hh]
  unfold triangleMain
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (2*(B : ℝ))⁻¹)]
  calc
    _ ≤ (2*(B : ℝ))⁻¹*(44*(B : ℝ)^2/(1+t^2)) := mul_le_mul_of_nonneg_left hl (by positivity)
    _ = _ := by field_simp; ring

lemma divisorTriangle_main_eq (t : ℝ) (B d : ℕ) :
    (((d : ℝ)*(2*B))⁻¹ : ℝ) • triangleMellin t B (2*B) =
      ((d : ℝ)⁻¹ : ℝ) • triangleMain t B := by
  rw [triangleMain, smul_smul]
  simp only [mul_inv_rev, mul_comm]

lemma divisorTriangle_low_uniform (t : ℝ) (u d : ℕ) (hu : 1 ≤ u) (hd : 0 < d)
    (hdB : d ≤ u^8) (ht : |t| ≤ (u : ℝ)^7) :
    ‖divisorTriangle t (u^8) d - ((d : ℝ)⁻¹ : ℝ) • triangleMain t (u^8)‖ ≤ 11*(u : ℝ)^7 := by
  have hu0 : 0 < u := by omega
  have hB : 0 < u^8 := pow_pos hu0 _
  have hb : (0 : ℝ) < (u^8 : ℕ) := by positivity
  have hh := divisorTriangle_low_error t (u^8) d hB hd
  rw [divisorTriangle_main_eq] at hh
  have hN : ((6*u^8/d+1 : ℕ) : ℝ)*d ≤ 7*(u^8 : ℕ) := by
    have hg := Nat.div_mul_le_self (6*u^8) d
    have hh : (6*u^8/d+1)*d ≤ 7*u^8 := by nlinarith
    exact_mod_cast hh
  have hU : (1 : ℝ) ≤ (u : ℝ)^7 := one_le_pow₀ (by exact_mod_cast hu)
  calc
    _ ≤ _ := hh
    _ ≤ 7*(u^8 : ℕ)*((2*((u^8 : ℕ) : ℝ))⁻¹+|t|/(u^8 : ℕ)) := by gcongr
    _ = 7/2+7*|t| := by field_simp
    _ ≤ _ := by linarith

theorem divisorTriangle_uniform (t : ℝ) (u d : ℕ) (hu : 1 ≤ u) (hd : 0 < d)
    (hdB : d ≤ u^8) (ht : |t| ≤ (u : ℝ)^10) :
    ‖divisorTriangle t (u^8) d - ((d : ℝ)⁻¹ : ℝ) • triangleMain t (u^8)‖ ≤ 1600*(u : ℝ)^7 := by
  have hu0 : 0 < u := by omega
  have hu' : (1 : ℝ) ≤ u := by exact_mod_cast hu
  by_cases hlo : |t| ≤ (u : ℝ)^7
  · exact (divisorTriangle_low_uniform t u d hu hd hdB hlo).trans (by gcongr; norm_num)
  have hhi : (u : ℝ)^7 ≤ |t| := le_of_lt (lt_of_not_ge hlo)
  have hdisc := divisorTriangle_high_power t u d hu hd hdB hhi ht
  have hmain := triangleMain_bound t (u^8) (pow_pos hu0 _)
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hh : (u : ℝ)^7 ≤ 1+t^2 := by
    have ha : |t|^2 = t^2 := sq_abs t
    nlinarith [sq_nonneg (|t|-1)]
  have hsm : ‖((d : ℝ)⁻¹ : ℝ) • triangleMain t (u^8)‖ ≤ 22*(u : ℝ)^7 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (d : ℝ)⁻¹)]
    calc
      _ ≤ 1 * (22*(u^8 : ℕ)/(1+t^2)) := by
        gcongr
        exact inv_le_one_of_one_le₀ hd'
      _ ≤ 22*(u : ℝ)^8/(u : ℝ)^7 := by simp only [Nat.cast_pow, one_mul]; gcongr
      _ = 22*(u : ℝ) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa using pow_le_pow_right₀ hu' (show 1 ≤ 7 by norm_num)) (by norm_num)
  calc
    _ ≤ ‖divisorTriangle t (u^8) d‖ + ‖((d : ℝ)⁻¹ : ℝ) • triangleMain t (u^8)‖ := norm_sub_le _ _
    _ ≤ 1500*(u : ℝ)^7+22*(u : ℝ)^7 := add_le_add hdisc hsm
    _ ≤ _ := by nlinarith [pow_nonneg (Nat.cast_nonneg u : (0 : ℝ) ≤ u) 7]

end OrdinaryLogIntegral

end

end OAI
