import OAI.NumberTheory.TwoPoint.Halasz.HalaszPoissonModes

namespace OAI

/-! Summing the stationary and nonstationary Poisson modes. -/
namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

noncomputable def halaszIntegerSquareMass : ℝ := ∑' k : ℤ, 1/(k:ℝ)^2

lemma halasz_integer_square_mass_nonneg : 0 ≤ halaszIntegerSquareMass :=
  tsum_nonneg (fun _ => by positivity)

theorem halasz_triangle_poisson_bound (N u : ℝ) (hN : 0 < N) :
    ‖∑' n : ℤ, halaszTriangleFunction N u 0 n‖ ≤
      18600*N/(1+u^2) + (440/Real.pi)*Real.sqrt |u| +
        (512/(N*(2*Real.pi)^2))*halaszIntegerSquareMass := by
  let R := 2*|u|/(Real.pi*N)
  let S := halaszNearModes R
  let Z := 18600*N/(1+u^2)
  let B := 110*N/Real.sqrt |u|
  let C := 512/(N*(2*Real.pi)^2)
  let a : ℤ → ℝ := fun k => if k=0 then Z else 0
  let b : ℤ → ℝ := fun k => if k ∈ S then B else 0
  let c : ℤ → ℝ := fun k => C*(1/(k:ℝ)^2)
  have ha : Summable a := summable_of_ne_finset_zero (s := {0}) (by
    intro k hk
    dsimp [a]
    simp only [mem_singleton] at hk
    exact ite_eq_right hk)
  have hb : Summable b := summable_of_ne_finset_zero (s := S) (by
    intro k hk
    exact ite_eq_right hk)
  have hc : Summable c :=
    (Real.summable_one_div_int_pow.mpr (by norm_num : 1<2)).mul_left C
  have hterm (k : ℤ) : ‖halaszTriangleIntegral N u (2*Real.pi*k)‖ ≤ a k+b k+c k := by
    by_cases hk : k=0
    · subst k
      simpa [a,b,c,Z,S,halasz_mem_near_modes] using halasz_triangle_zero N u hN
    have hkR : (k:ℝ) ≠ 0 := by exact_mod_cast hk
    have hp : 0 < |(k:ℝ)| := abs_pos.mpr hkR
    have hv : 2*Real.pi*(k:ℝ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hkR
    by_cases hs : k ∈ S
    · have hks := (halasz_mem_near_modes R k).mp hs
      have hu : u ≠ 0 := by
        intro hu
        subst u
        have hR : R=0 := by simp [R]
        rw [hR] at hks
        linarith [hks.2]
      have h := halasz_triangle_stationary_abs N u (2*Real.pi*k) hN hu
      have hcn : 0 ≤ c k := by dsimp [c,C]; positivity
      simpa only [a,b,ite_eq_right hk,ite_eq_left hs,zero_add] using h.trans (le_add_of_nonneg_right hcn)
    · have hout : R < |(k:ℝ)| := by
        by_contra hn
        exact hs ((halasz_mem_near_modes R k).mpr ⟨hk,le_of_not_gt hn⟩)
      have hfar : 4*|u| ≤ N*|2*Real.pi*(k:ℝ)| := by
        have hpN : 0 < Real.pi*N := mul_pos Real.pi_pos hN
        have hh := (div_lt_iff₀ hpN).mp hout
        rw [abs_mul, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
        nlinarith
      have h := halasz_triangle_far N u (2*Real.pi*k) hN hv hfar
      have he : 512/(N*(2*Real.pi*(k:ℝ))^2) = c k := by dsimp [c,C]; ring
      simpa only [a,b,ite_eq_right hk,ite_eq_right hs,zero_add] using h.trans_eq he
  have hnorm : Summable (fun k : ℤ => ‖halaszTriangleIntegral N u (2*Real.pi*k)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm ((ha.add hb).add hc)
  have hZA : (∑' k : ℤ, a k) = Z := by
    rw [tsum_eq_sum (s := {0}) (fun k hk => by
      dsimp [a]
      simp only [mem_singleton] at hk
      exact ite_eq_right hk)]
    simp [a]
  have hSB : (∑' k : ℤ, b k) = (S.card:ℝ)*B := by
    rw [tsum_eq_sum (s := S) (fun k hk => ite_eq_right hk)]
    simp
  have hTC : (∑' k : ℤ, c k) = C*halaszIntegerSquareMass := by
    exact tsum_mul_left
  have hcard : (S.card:ℝ) ≤ 2*R :=
    halasz_near_modes_card R (by dsimp [R]; positivity)
  have hmode : (2*R)*B = (440/Real.pi)*Real.sqrt |u| := by
    by_cases hu : u=0
    · subst u
      simp [R,B]
    have hsu : 0 < Real.sqrt |u| := Real.sqrt_pos.mpr (abs_pos.mpr hu)
    have he := Real.sq_sqrt (abs_nonneg u)
    dsimp [R,B]
    field_simp
    nlinarith
  rw [halasz_triangle_poisson N u hN]
  calc
    _ ≤ ∑' k : ℤ, ‖halaszTriangleIntegral N u (2*Real.pi*k)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k : ℤ, (a k+b k+c k) := hnorm.tsum_le_tsum hterm ((ha.add hb).add hc)
    _ = Z+(S.card:ℝ)*B+C*halaszIntegerSquareMass := by
      rw [(ha.add hb).tsum_add hc,ha.tsum_add hb,hZA,hSB,hTC]
    _ ≤ Z+(2*R)*B+C*halaszIntegerSquareMass := by gcongr
    _ = _ := by rw [hmode]

end TwoPointCorrelations

end OAI
