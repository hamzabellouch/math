import Mathlib.Analysis.SpecialFunctions.Exp
import OAI.Combinatorics.Progressions.Estimates.AllocatedUnitSiteFactors

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem unitSiteLipschitzBudget_le_exp {A : Type*} [Fintype A]
    (L K : ℝ≥0) (C : A → ℝ≥0) (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) {P : ℝ}
    (hL : (L : ℝ) ≤ Real.exp P) (hK : (K : ℝ) ≤ Real.exp P)
    (hC : ∀ a, (C a : ℝ) ≤ Real.exp P) (hW : (∑ a, w a) ≤ Real.exp P) :
    (L : ℝ) * ((K : ℝ) * ∑ a, (C a : ℝ) * w a) ≤ Real.exp (4 * P) := by
  have hs : (∑ a, (C a : ℝ) * w a) ≤ Real.exp (2 * P) := by
    calc
      _ ≤ ∑ a, Real.exp P * w a := Finset.sum_le_sum (fun a _ =>
        mul_le_mul_of_nonneg_right (hC a) (hw a))
      _ = Real.exp P * ∑ a, w a := (Finset.mul_sum _ _ _).symm
      _ ≤ Real.exp P * Real.exp P := mul_le_mul_of_nonneg_left hW (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hs0 : 0 ≤ ∑ a, (C a : ℝ) * w a := Finset.sum_nonneg (fun a _ => mul_nonneg (C a).coe_nonneg (hw a))
  calc
    _ ≤ Real.exp P * (Real.exp P * Real.exp (2 * P)) :=
      mul_le_mul hL (mul_le_mul hK hs hs0 (Real.exp_pos _).le)
        (mul_nonneg K.coe_nonneg hs0) (Real.exp_pos _).le
    _ = _ := by simp only [← Real.exp_add]; congr 1; ring

theorem unitSiteCoefficientMass_le_exp {T : Type*} [Fintype T]
    (c : T → ℂ) (N : ℕ) {Q : ℝ} (hc : (∑ i, ‖c i‖) ≤ Real.exp Q) :
    (∑ i, ‖c i * (2 : ℂ) ^ N‖) ≤ Real.exp (Q + N) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (2 : ℝ) ^ N ≤ Real.exp (N : ℝ) := by
    calc
      _ ≤ (Real.exp 1) ^ N := pow_le_pow_left₀ (by norm_num) htwo N
      _ = _ := by rw [← Real.exp_nat_mul]; simp only [mul_one]
  have hn : ‖(2 : ℂ) ^ N‖ = (2 : ℝ) ^ N := by rw [norm_pow]; norm_num
  calc
    _ = (∑ i, ‖c i‖) * (2 : ℝ) ^ N := by simp_rw [norm_mul, hn]; rw [Finset.sum_mul]
    _ ≤ Real.exp Q * Real.exp (N : ℝ) := mul_le_mul hc hp (by positivity) (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem complex_coefficient_two_power_mass {T : Type*} [Fintype T]
    (a : T → ℂ) (q : ℕ) {M : ℝ} (ha : (∑ i, ‖a i‖) ≤ Real.exp M) :
    (∑ i, ‖a i * (2 : ℂ) ^ q‖) ≤ Real.exp (M + q) := by
  exact unitSiteCoefficientMass_le_exp a q ha

theorem ambient_site_lipschitz_weight_bound {m : ℕ} {J : Fin m → Type*}
    [∀ j, Fintype (J j)] (C : Fin m → ℝ≥0) {P : ℝ}
    (hm : (m : ℝ) ≤ P) (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hC : ∀ j, (C j : ℝ) ≤ Real.exp P) :
    Real.exp P * (∑ j, (C j : ℝ) * Fintype.card (J j)) ≤ Real.exp (4 * P) := by
  have hPE : P ≤ Real.exp P := by linarith [Real.add_one_le_exp P]
  have hsum : (∑ j, (C j : ℝ) * Fintype.card (J j)) ≤ Real.exp (3 * P) := by
    calc
      _ ≤ ∑ _j : Fin m, Real.exp (2 * P) := Finset.sum_le_sum (fun j _ => by
        calc
          _ ≤ Real.exp P * Real.exp P := mul_le_mul (hC j) ((hJ j).trans hPE)
            (by positivity) (Real.exp_nonneg _)
          _ = _ := by rw [← Real.exp_add]; congr 1; ring)
      _ = (m : ℝ) * Real.exp (2 * P) := by simp
      _ ≤ Real.exp P * Real.exp (2 * P) := mul_le_mul_of_nonneg_right (hm.trans hPE) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ ≤ Real.exp P * Real.exp (3 * P) := mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
