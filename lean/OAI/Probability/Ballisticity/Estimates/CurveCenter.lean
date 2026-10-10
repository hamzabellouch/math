import Mathlib
import OAI.Probability.Ballisticity.Estimates.CurvePolicyMaximal

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma curvePolicy_mean_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (b : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (dummy : Lattice d) (hd : signedCoordinate f dummy = b H) :
    |(∫ u, signedCoordinate f u ∂(curvePolicy_average ν (realPosition (step e)) f b B hH E hδ hα dummy).toMeasure)-b H| ≤ B :=
  abs_mean_sub_le _ _ (measurable_of_countable _) _ _
    (curvePolicy_average_lateral_bound ν e f b hB hH E hδ hα dummy hd)

lemma median_line_mean_bound (b : ℕ → ℝ) {H : ℕ} (hH : 0 < H) {m B D : ℝ}
    (hB : 0 ≤ B) (hm : |m-b H| ≤ B)
    (hb : ∀ j ≤ H, |b j-(j:ℝ)*b H/H| ≤ D) :
    ∀ j ≤ H, |b j-(j:ℝ)*(m/H)| ≤ D+B := by
  intro j hj
  have hHp : (0:ℝ)<H := by exact_mod_cast hH
  have hratio : 0 ≤ (j:ℝ)/H := by positivity
  have hratio1 : (j:ℝ)/H ≤ 1 := (div_le_one hHp).mpr (by exact_mod_cast hj)
  calc
    _ = |(b j-(j:ℝ)*b H/H)+((j:ℝ)/H)*(b H-m)| := by congr 1; ring
    _ ≤ |b j-(j:ℝ)*b H/H|+|((j:ℝ)/H)*(b H-m)| := abs_add_le _ _
    _ = |b j-(j:ℝ)*b H/H|+((j:ℝ)/H)*|m-b H| := by rw [abs_mul,abs_of_nonneg hratio,abs_sub_comm (b H) m]
    _ ≤ D+B := add_le_add (hb j hj) ((mul_le_mul_of_nonneg_left hm hratio).trans (mul_le_of_le_one_left hB hratio1))

end DirectionalTransience

end

end

end OAI
