import OAI.NumberTheory.Ostmann.QuadraticCenter.DistinctCoefficientBounds

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter

def commonCenterCutoff (Z : ℕ) : ℕ := ⌊(Z : ℝ) ^ (3 / 5 : ℝ)⌋₊

def commonCenterMomentScale (J Z k : ℕ) : ℝ :=
  (J : ℝ)^k * (Z : ℝ)^(-(7 / 50 : ℝ))

def commonCenterMass (J Z k : ℕ) : ℕ := ⌊commonCenterMomentScale J Z k / 2⌋₊

theorem descFactorial_half_pow_le {J k : ℕ} (hk : 1 ≤ k)
    (hsmall : 2 * (k : ℝ)^2 ≤ J) :
    (J : ℝ)^k / 2 ≤ (J.descFactorial k : ℝ) := by
  have herr : (J : ℝ)^k ≤ (J.descFactorial k : ℝ) + (k : ℝ)^2 * (J : ℝ)^(k-1) := by
    exact_mod_cast pow_le_descFactorial_add J k
  have hp : (J : ℝ) * (J : ℝ)^(k-1) = (J : ℝ)^k := by
    rw [←pow_succ',Nat.sub_add_cancel hk]
  have hh := mul_le_mul_of_nonneg_right hsmall (pow_nonneg (Nat.cast_nonneg J) (k-1))
  rw [hp] at hh
  nlinarith

theorem commonCenterMass_bounds (J Z k : ℕ) (h : 4 ≤ commonCenterMomentScale J Z k) :
    0 < commonCenterMass J Z k ∧
      commonCenterMomentScale J Z k / 4 ≤ (commonCenterMass J Z k : ℝ) ∧
      (commonCenterMass J Z k : ℝ) ≤ commonCenterMomentScale J Z k / 2 := by
  have hl := Nat.lt_floor_add_one (commonCenterMomentScale J Z k / 2)
  have hu := Nat.floor_le (show 0 ≤ commonCenterMomentScale J Z k / 2 by linarith)
  change commonCenterMomentScale J Z k / 2 < (commonCenterMass J Z k : ℝ)+1 at hl
  change (commonCenterMass J Z k : ℝ) ≤ commonCenterMomentScale J Z k / 2 at hu
  have hm : (0 : ℝ) < commonCenterMass J Z k := by linarith
  exact ⟨by exact_mod_cast hm,by linarith,hu⟩

theorem commonCenterMass_moment_input (J Z k lower upper : ℕ)
    (hscale : 4 ≤ commonCenterMomentScale J Z k)
    (hlower : (commonCenterCutoff Z : ℝ)^10 * (lower : ℝ) ≤
      commonCenterMomentScale J Z k / 4)
    (hupper : commonCenterMomentScale J Z k ≤ (upper : ℝ)) :
    0 < commonCenterMass J Z k ∧
      commonCenterMass J Z k + commonCenterCutoff Z^10 * lower ≤ upper := by
  obtain ⟨hpos,hmlo,hmhi⟩ := commonCenterMass_bounds J Z k hscale
  refine ⟨hpos,?_⟩
  have hh : (commonCenterMass J Z k : ℝ) +
      (commonCenterCutoff Z : ℝ)^10 * (lower : ℝ) ≤ (upper : ℝ) := by linarith
  exact_mod_cast hh

end Ostmann.QuadraticCenter

end

end OAI
