import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGcdCorrectionPowerSaving
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticMainPowerCost
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallGcdAssembly

namespace OAI

/-! # The complete small-gcd comparison with a proved small-power error -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_small_gcd_growth {ξ η : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ M R D K : ℕ, 0 < M → 0 < R → Squarefree D → Odd D → D < R → 0 < K →
      (K : ℝ) ≤ ((M : ℝ) * R) ^ 3 →
      2 * (2 * (R : ℝ)) ^ 2 * (((M : ℝ) * R) ^ η) ≤ (M : ℝ) * ((K : ℝ) + 1) →
      ∀ v : ℕ → ℂ, (∀ n < R, v n = 0) →
        ‖quadraticRoughGcdMoment M (2 * R) K D v‖ ≤
          C * ((M : ℝ) * R) ^ (36 * η) * (D : ℝ) ^ 4 *
            ((M : ℝ) + R + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2) +
              Real.sqrt M * R / Real.sqrt K) * quadraticSieveEnergy (2 * R) v := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hc⟩ := quadratic_small_gcd_comparison h hη hη 1
  obtain ⟨C₃, hC₃, hcorr⟩ := quadratic_gcd_corrections_power_bound h hξ hξ' hη
  let C := 2 * C₁ * 2 ^ (3 * η) + C₂ + C₃
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro M R D K hM hR hD ho hDR hK hKX hcut v hv
  let X := (M : ℝ) * R
  let V := (M : ℝ) + R + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2) +
    Real.sqrt M * R / Real.sqrt K
  let F := X ^ (36 * η) * (D : ℝ) ^ 4 * V
  let E := quadraticSieveEnergy (2 * R) v
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hM₁ : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hR₁ : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hD₁ : (1 : ℝ) ≤ D := by exact_mod_cast Nat.pos_of_ne_zero hD.ne_zero
  have hX : 1 ≤ X := one_le_mul_of_one_le_of_one_le hM₁ hR₁
  have hRX : (R : ℝ) ≤ X := by dsimp [X]; nlinarith
  have hV₁ : 1 ≤ V := by
    dsimp [V]
    have : 0 ≤ Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2) := by positivity
    have : 0 ≤ Real.sqrt M * R / Real.sqrt K := by positivity
    linarith
  have hF₁ : 1 ≤ F := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hX (by positivity)) (one_le_pow₀ hD₁)) hV₁
  have hb := hc M R K D hM hR hD ho hDR hK (X ^ η) le_rfl hcut hKX v
    (fun n _ hn => hv n hn)
  have hcoef := quadratic_main_power_cost hη.le hX (Nat.cast_nonneg R) (Nat.cast_nonneg D)
    (Nat.cast_nonneg K) hRX (by exact_mod_cast hDR.le) hKX
  have hexp := quadratic_gcd_main_exponent hξ' hK (Nat.pos_of_ne_zero hD.ne_zero)
    (2 * (R : ℝ)) (by positivity)
  have hscale : Real.sqrt M / Real.sqrt K * ((K : ℝ) ^ ξ + 2 * R) ≤ 2 * V := by
    rw [quadratic_main_scale (by exact_mod_cast hK)]
    dsimp [V]
    have : 0 ≤ Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2) := by positivity
    linarith
  have hmain : C₁ * (((K * D ^ 2 : ℕ) : ℝ) * (2 * R)) ^ (2 * η) * (D : ℝ) ^ η *
      (Real.sqrt M / Real.sqrt K) * (((K * D ^ 2 : ℕ) : ℝ) ^ ξ + 2 * R) ≤
      (2 * C₁ * 2 ^ (3 * η)) * F := by
    calc
      _ = C₁ * ((((K * D ^ 2 : ℕ) : ℝ) * (2 * R)) ^ (2 * η) * (D : ℝ) ^ η) *
          ((Real.sqrt M / Real.sqrt K) * (((K * D ^ 2 : ℕ) : ℝ) ^ ξ + 2 * R)) := by ring
      _ ≤ C₁ * (2 ^ (3 * η) * X ^ (36 * η)) *
          ((Real.sqrt M / Real.sqrt K) * ((D : ℝ) ^ 4 * ((K : ℝ) ^ ξ + 2 * R))) := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_left _ hC₁.le
          simpa only [Nat.cast_mul, Nat.cast_pow] using hcoef
        · exact mul_le_mul_of_nonneg_left hexp (by positivity)
        · positivity
        · positivity
      _ = (C₁ * 2 ^ (3 * η) * X ^ (36 * η) * (D : ℝ) ^ 4) *
          ((Real.sqrt M / Real.sqrt K) * ((K : ℝ) ^ ξ + 2 * R)) := by ring
      _ ≤ (C₁ * 2 ^ (3 * η) * X ^ (36 * η) * (D : ℝ) ^ 4) * (2 * V) := by gcongr
      _ = _ := by dsimp [F]; ring
  have herr : C₂ / X ^ (1 : ℕ) ≤ C₂ * F := by
    rw [pow_one]
    exact (div_le_self hC₂.le hX).trans (le_mul_of_one_le_right hC₂.le hF₁)
  have hco := hcorr M R D K hM hR hD ho hDR.le hK hKX v hv
  have hcor : ‖quadraticGcdMomentCorrections M R K D (X ^ η) v‖ ≤ C₃ * F * E := by
    apply hco.trans
    calc
      _ = C₃ * X ^ (36 * η) * (D : ℝ) ^ 2 *
          ((M : ℝ) + R + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2)) * E := by ring
      _ ≤ C₃ * X ^ (36 * η) * (D : ℝ) ^ 4 * V * E := by
        apply mul_le_mul_of_nonneg_right _ hE
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD₁ (by norm_num : 2 ≤ (4 : ℕ))) (by positivity)
        · change (M : ℝ) + R + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2) ≤ V
          dsimp [V]
          exact le_add_of_nonneg_right (by positivity)
        · positivity
        · positivity
      _ = C₃ * F * E := by dsimp [F]; ring
  have hmE := mul_le_mul_of_nonneg_right hmain hE
  have heE := mul_le_mul_of_nonneg_right herr hE
  calc
    _ ≤ (2 * C₁ * 2 ^ (3 * η) + C₂ + C₃) * F * E := by
      change ‖quadraticRoughGcdMoment M (2 * R) K D v‖ ≤
        (_ + C₂ / X ^ (1 : ℕ)) * E + ‖quadraticGcdMomentCorrections M R K D (X ^ η) v‖ at hb
      nlinarith only [hb, hmE, heE, hcor]
    _ = _ := by dsimp [C, F, X, V, E]; ring

end Ostmann

end OAI
