import OAI.NumberTheory.Ostmann.Quadratic.QuadraticMiddleDivisor
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSqrtCoefficients

namespace OAI

/-! # The actual Mobius and square-root weights of the divisor corrections -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

theorem quadratic_moebius_root_weight {D B d b : ℕ}
    (hD : 0 < D) (hB : 0 < B) (hd : D ≤ d) (hb : B ≤ b) :
    ‖((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)‖ ≤
      1 / ((D : ℝ) * Real.sqrt B) := by
  have hμ : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  have hBr : 0 < (B : ℝ) := by exact_mod_cast hB
  have hdr : (D : ℝ) ≤ d := by exact_mod_cast hd
  have hbr : (B : ℝ) ≤ b := by exact_mod_cast hb
  rw [norm_div, norm_div, Complex.norm_natCast, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ (1 / (D : ℝ)) / Real.sqrt B := by
      have hfirst : ‖(ArithmeticFunction.moebius d : ℂ)‖ / (d : ℝ) ≤ 1 / (D : ℝ) :=
        div_le_div₀ (by norm_num : (0 : ℝ) ≤ 1) hμ hDr hdr
      exact div_le_div₀ (div_nonneg (by norm_num) hDr.le)
        hfirst (Real.sqrt_pos.2 hBr) (Real.sqrt_le_sqrt hbr)
    _ = _ := by ring

theorem quadratic_correction_band_weight (F : ℕ → ℕ → ℂ) {D B : ℕ}
    (hD : 0 < D) (hB : 0 < B) (U V : ℝ) :
    ‖∑ d ∈ (Finset.Ioc D (2 * D)).filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
      ∑ b ∈ (oddSquarefreeRange (2 * B)).filter (fun b => B ≤ b),
        (((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)) * F d b‖ ≤
      (1 / ((D : ℝ) * Real.sqrt B)) *
        ∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B), ‖F d b‖ := by
  let S := (Finset.Ioc D (2 * D)).filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V)
  let R := (oddSquarefreeRange (2 * B)).filter (fun b => B ≤ b)
  let c : ℝ := 1 / ((D : ℝ) * Real.sqrt B)
  calc
    _ ≤ ∑ d ∈ S, ∑ b ∈ R,
        ‖(((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)) * F d b‖ := by
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ d ∈ S, ∑ b ∈ R, c * ‖F d b‖ := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro b hb
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (quadratic_moebius_root_weight hD hB
          (Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1).1.le
          (Finset.mem_filter.mp hb).2) (norm_nonneg _)
    _ ≤ ∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B), c * ‖F d b‖ := by
      apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..)
        (fun d _ _ => Finset.sum_nonneg (fun b _ => by dsimp [c]; positivity))).trans
      apply Finset.sum_le_sum
      intro d _
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..)
        (fun b _ _ => by dsimp [c]; positivity)
    _ = _ := by simp only [← Finset.mul_sum]; rfl

theorem quadratic_middle_correction_band (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    (M : ℝ) (e N L : ℕ) (v w : ℕ → ℂ) {D B : ℕ}
    (hD : 0 < D) (hB : 0 < B) (U V T : ℝ)
    (hbound : (∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
      ‖quadraticMiddleWindow ρ a ha M e N d v w b L‖) ≤ T) :
    ‖∑ d ∈ (Finset.Ioc D (2 * D)).filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
      ∑ b ∈ (oddSquarefreeRange (2 * B)).filter (fun b => B ≤ b),
        (((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)) *
          quadraticMiddleWindow ρ a ha M e N d v w b L‖ ≤
      T / ((D : ℝ) * Real.sqrt B) := by
  apply (quadratic_correction_band_weight
    (fun d b => quadraticMiddleWindow ρ a ha M e N d v w b L) hD hB U V).trans
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using
    mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ 1 / ((D : ℝ) * Real.sqrt B))

end Ostmann

end OAI
