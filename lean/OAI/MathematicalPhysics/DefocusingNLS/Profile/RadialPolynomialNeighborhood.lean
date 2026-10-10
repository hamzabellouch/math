import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPolynomialCircleBound

namespace OAI

/-! A common subunit neighborhood for bounded finite-degree exterior expansions. -/

open Polynomial Set
namespace DefocusingNLS

theorem radialPolynomial_eval_near_constant (P : ℂ[X]) (d : ℕ) (hd : P.natDegree ≤ d)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ k, k ≤ d → ‖P.coeff k‖ ≤ B)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖P.eval z-P.coeff 0‖ ≤ (d : ℝ)*B*‖z‖ := by
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hd) z,Finset.sum_range_succ']
  simp only [pow_zero,mul_one,add_sub_cancel_right]
  calc
    _ ≤ ∑ k ∈ Finset.range d, ‖P.coeff (k+1)*z^(k+1)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range d, B*‖z‖ := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul,norm_pow,pow_succ]
      have hp : ‖z‖^k ≤ 1 := pow_le_one₀ (norm_nonneg _) hz
      have hc := hb (k+1) (by have := Finset.mem_range.mp hk; omega)
      calc
        _ ≤ B*(1*‖z‖) := by gcongr
        _ = _ := by ring
    _ = _ := by simp [mul_assoc]

theorem exists_radialPolynomial_subunit_circle (d : ℕ) (B ρ₀ ρ₁ : ℝ)
    (hB : 0 ≤ B) (hρ : ρ₀ < ρ₁) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ P : ℂ[X], P.natDegree ≤ d →
      ‖P.coeff 0‖ ≤ ρ₀ → (∀ k, k ≤ d → ‖P.coeff k‖ ≤ B) →
      ∀ z : ℂ, ‖z‖ ≤ ε → ‖P.eval z‖ ≤ ρ₁ := by
  let D : ℝ := (d : ℝ)*B
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let ε : ℝ := min 1 ((ρ₁-ρ₀)/(2*(1+D)))
  have he : 0 < ε := lt_min (by norm_num) (div_pos (sub_pos.mpr hρ) (by positivity))
  have he1 : ε ≤ 1 := min_le_left _ _
  have he2 : ε*(2*(1+D)) ≤ ρ₁-ρ₀ :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  refine ⟨ε,he,he1,?_⟩
  intro P hdeg hzero hcoeff z hz
  have hp := radialPolynomial_eval_near_constant P d hdeg B hB hcoeff z (hz.trans he1)
  have hn := norm_le_norm_sub_add (P.eval z) (P.coeff 0)
  have hDE := mul_le_mul_of_nonneg_left hz hD
  change D*‖z‖ ≤ D*ε at hDE
  change ‖P.eval z-P.coeff 0‖ ≤ D*‖z‖ at hp
  nlinarith

end DefocusingNLS

end OAI
