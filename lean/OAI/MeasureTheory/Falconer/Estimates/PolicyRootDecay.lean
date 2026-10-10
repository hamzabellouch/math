import OAI.MeasureTheory.Falconer.Recursion.PolicyWeightedRecursion

namespace OAI

/-! # Absorbing the finite branch factor into the root potential gain -/

namespace Falconer

/-- The fixed branching factor costs an arbitrarily small power. -/
theorem eventual_policy_root_decay (D : ℕ) {gain : ℝ}
    (hgain : 0 < gain) (hgain1 : gain ≤ 1) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ E x : ℝ, E ≤ -2*gain →
      x ≤ 4^(D+1)*(((2:ℝ)^N)^E+((2:ℝ)^N)^(-10:ℝ)) →
      x ≤ ((2:ℝ)^N)^(-gain) := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hgain (2*4^(D+1))
  refine ⟨N₀,?_⟩
  intro N hN E x hE hx
  have hR : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  have hterm : ((2:ℝ)^N)^E ≤ ((2:ℝ)^N)^(-2*gain) :=
    Real.rpow_le_rpow_of_exponent_le hR hE
  have herr : ((2:ℝ)^N)^(-10:ℝ) ≤ ((2:ℝ)^N)^(-2*gain) :=
    Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  calc
    x ≤ 4^(D+1)*(((2:ℝ)^N)^E+((2:ℝ)^N)^(-10:ℝ)) := hx
    _ ≤ 4^(D+1)*(((2:ℝ)^N)^(-2*gain)+((2:ℝ)^N)^(-2*gain)) := by gcongr
    _ = (2*4^(D+1))*((2:ℝ)^N)^(-2*gain) := by ring
    _ ≤ ((2:ℝ)^N)^gain*((2:ℝ)^N)^(-2*gain) :=
      mul_le_mul_of_nonneg_right (hN₀ N hN) (by positivity)
    _ = ((2:ℝ)^N)^(-gain) := by
      rw [← Real.rpow_add (by positivity)]
      congr 1
      ring

end Falconer

end OAI
