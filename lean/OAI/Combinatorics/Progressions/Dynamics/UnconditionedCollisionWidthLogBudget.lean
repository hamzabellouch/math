import OAI.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry

namespace OAI

section

namespace Erdos3

theorem unconditionedCollisionWidth_le_exp {K : Type*} [Fintype K] [DecidableEq K]
    (P : K → ℕ) [∀ k, NeZero (P k)] {σ S T : ℝ} (hσ : 0 < σ)
    (hσinv : σ⁻¹ ≤ Real.exp S)
    (hcard : (Fintype.card (∀ k, ZMod (P k)) : ℝ) ≤ Real.exp T) :
    unconditionedCollisionWidth P σ ≤ Real.exp (2 * T + S + 5) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hconstant : (32 : ℝ) ≤ Real.exp 5 := by
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo 5
    rw [← Real.exp_nat_mul] at hpow
    norm_num at hpow ⊢
    exact hpow
  calc
    unconditionedCollisionWidth P σ =
        32 * (Fintype.card (∀ k, ZMod (P k)) : ℝ)^2 * σ⁻¹ := by
      rw [unconditionedCollisionWidth, div_eq_mul_inv]
    _ ≤ Real.exp 5 * (Real.exp T)^2 * Real.exp S := by gcongr
    _ = Real.exp (2 * T + S + 5) := by
      simp only [sq, ← Real.exp_add]
      congr 1
      ring

end Erdos3

end

end OAI
