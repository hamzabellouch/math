import OAI.NumberTheory.CubicMoment.Estimates.FiniteSieveDensity
import OAI.NumberTheory.CubicMoment.Estimates.UniformCoreBlockMoment

namespace OAI

/-! The norm and cardinality costs of the logarithmic square-divisor
truncation used in the positive variance term. -/
noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma squarefreeDivisorTruncation_card_le {D : ℝ} (hD : 0 ≤ D) :
    ((squarefreeDivisorTruncation D).card:ℝ) ≤ 18*D := by
  apply le_trans _ (nonzeroNormBall_card_le hD)
  have hsub : squarefreeDivisorTruncation D ⊆ nonzeroNormBall D := by
    intro c hc
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1
  exact_mod_cast Finset.card_le_card hsub

lemma squarefreeTruncation_join_norm {D : ℝ} (hD : 0 ≤ D)
    {c d : Eisenstein} (hc : c ∈ squarefreeDivisorTruncation D)
    (hd : d ∈ squarefreeDivisorTruncation D) :
    norm (primarySquarefreeJoin c d) ≤ D^2 := by
  have hc' := mem_squarefreeDivisorTruncation.mp hc
  have hd' := mem_squarefreeDivisorTruncation.mp hd
  apply (primarySquarefreeJoin_norm_le hc'.1 hd'.1).trans
  exact (mul_le_mul hc'.2.2 hd'.2.2 (norm_nonneg d) hD).trans_eq (by ring)

lemma eventually_logPower_le_rpow {a : ℝ} (ha : 0 < a) (b : ℕ) :
    ∀ᶠ X : ℝ in atTop, (1+Real.log X)^b ≤ X^a := by
  filter_upwards [negative_power_log_saving ha b,eventually_ge_atTop (1:ℝ)] with X hX hX1
  have hXp : 0 < X := zero_lt_one.trans_le hX1
  have hz : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX1]
  apply (inv_le_inv₀ (Real.rpow_pos_of_pos hXp a) (pow_pos hz b)).mp
  simpa only [Real.rpow_neg hXp.le,one_div] using hX

end CubicFirstMoment

end

end OAI
