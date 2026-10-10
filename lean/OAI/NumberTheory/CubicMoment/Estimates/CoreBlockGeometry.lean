import OAI.NumberTheory.CubicMoment.Estimates.CubicFrequencyMassSplit

namespace OAI

/-! The geometric cube cutoff in each actual core block has precisely
the mass scale needed by the noncube moment estimates. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma coreDyadicCubeFactors_spec {B : ℝ} (hB : 0 ≤ B) {i j : ℕ} {c : Eisenstein}
    (hc : c ∈ coreDyadicCubeFactors B i j) :
    c ≠ 0 ∧ norm c^3*coreDyadicConductor i j ≤ B := by
  obtain ⟨hcN,hc0⟩ := mem_nonzeroNormBall.mp hc
  have hD := coreDyadicConductor_pos i j
  refine ⟨hc0,?_⟩
  have hp := pow_le_pow_left₀ (norm_nonneg c) hcN 3
  rw [rpow_third_cube (div_nonneg hB hD.le)] at hp
  exact (le_div_iff₀ hD).mp hp

lemma rpow_eight_third : (8:ℝ)^(1/3:ℝ) = 2 := by
  rw [show (8:ℝ) = (2:ℝ)^3 by norm_num,← Real.rpow_natCast (2:ℝ) 3,
    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

lemma coreDyadicCubeFactors_card_eight_weight {B : ℝ} (hB : 0 ≤ B) (i j : ℕ) :
    ((coreDyadicCubeFactors B i j).card:ℝ)*(8*coreDyadicConductor i j)^(1/3:ℝ) ≤
      36*B^(1/3:ℝ) := by
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 8) (coreDyadicConductor_pos i j).le,
    rpow_eight_third]
  nlinarith [coreDyadicCubeFactors_card_weight hB i j]

end CubicFirstMoment

end

end OAI
