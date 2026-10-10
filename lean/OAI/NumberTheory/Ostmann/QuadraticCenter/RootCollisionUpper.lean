import OAI.NumberTheory.Ostmann.QuadraticCenter.RootCollisionUpperBasic

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem rootCollisionProbability_weighted_le_scale (X η : ℝ) (hX : 1 < X) (hη : 0 ≤ η)
    (U : Finset ℕ) (hU : U.Nonempty)
    (hcard : X^(1/2-3*η) ≤ (U.card:ℝ))
    (hdiam : ∀ a ∈ U, ∀ b ∈ U, |(a:ℝ)-b| ≤ X^(1/2+η)) :
    (∑ p ∈ (⌊X^(1/2-5*η)⌋₊:ℕ).primesLE,
      Real.log p * rootCollisionProbability U p) ≤
      (1/2+η)*Real.log X + Real.log 2 + Real.log 4 := by
  have hXp : 0 < X := by linarith
  have hD : 1 ≤ X^(1/2+η) := Real.one_le_rpow hX.le (by linarith)
  have hC : 0 < (U.card:ℝ) := by exact_mod_cast hU.card_pos
  have hQ : ((⌊X^(1/2-5*η)⌋₊:ℕ):ℝ) ≤ (U.card:ℝ) :=
    (Nat.floor_le (Real.rpow_nonneg hXp.le _)).trans
      ((Real.rpow_le_rpow_of_exponent_le hX.le (by linarith)).trans hcard)
  have hdiagonal : Real.log 4 * (⌊X^(1/2-5*η)⌋₊:ℕ) / (U.card:ℝ) ≤ Real.log 4 := by
    apply (div_le_iff₀ hC).2
    exact mul_le_mul_of_nonneg_left hQ (Real.log_nonneg (by norm_num))
  have hlog := log_ceil_le_log_add_log_two (X^(1/2+η)) hD
  rw [Real.log_rpow hXp] at hlog
  have hu := rootCollisionProbability_weighted_le_diameter U hU
    ⌊X^(1/2-5*η)⌋₊ (X^(1/2+η)) hD hdiam
  linarith

theorem rootCollisionProbability_pair_weighted_le_scale
    (X η : ℝ) (hX : 1 < X) (hη : 0 ≤ η)
    (U V : Finset ℕ) (hU : U.Nonempty) (hV : V.Nonempty)
    (hUcard : X^(1/2-3*η) ≤ (U.card:ℝ))
    (hVcard : X^(1/2-3*η) ≤ (V.card:ℝ))
    (hUdiam : ∀ a ∈ U, ∀ b ∈ U, |(a:ℝ)-b| ≤ X^(1/2+η))
    (hVdiam : ∀ a ∈ V, ∀ b ∈ V, |(a:ℝ)-b| ≤ X^(1/2+η)) :
    (∑ p ∈ (⌊X^(1/2-5*η)⌋₊:ℕ).primesLE,
      Real.log p * (rootCollisionProbability U p + rootCollisionProbability V p)) ≤
      (1+2*η)*Real.log X + (2*Real.log 2+2*Real.log 4) := by
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have h1 := rootCollisionProbability_weighted_le_scale X η hX hη U hU hUcard hUdiam
  have h2 := rootCollisionProbability_weighted_le_scale X η hX hη V hV hVcard hVdiam
  linarith

end Ostmann.QuadraticCenter

end

end OAI
