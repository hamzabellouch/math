import OAI.Combinatorics.EditApproximation.Geometry.InitialCones

namespace OAI

/-!
# The numerical locality test for initial cones

Any globally minimizing cone at a positive-cost query lies in the
algorithm's finite local scale interval and search radius. The inequalities
below use the actual seed factor and cone slope from Section 4.
-/

namespace EditApproximation

theorem initial_cone_locality_numeric {c centerCost Uq Ur distance b A F cone : ℚ}
    (hc : 0 < c) (hA : 1 ≤ A) (hF : 0 < F) (hb : 0 ≤ b)
    (hquery : c ≤ Uq ∧ Uq ≤ A * c)
    (hcenter : centerCost ≤ Ur ∧ Ur ≤ A * centerCost)
    (hcost : |c - centerCost| ≤ distance)
    (heligible : b / 2 ≤ Ur ∧ Ur ≤ 4 * A * b)
    (hconeLower : 32 * F * distance ≤ cone) (hconeUpper : cone ≤ 2 * F * c) :
    distance ≤ c / 16 ∧ Ur ≠ 0 ∧ Uq / (16 * A ^ 2) ≤ b ∧ b ≤ 4 * A * Uq ∧ distance ≤ Uq := by
  have hA0 : 0 < A := by linarith
  have hdist : distance ≤ c / 16 := by
    have hscaled : F * (16 * distance - c) ≤ 0 := by nlinarith
    have hdiff : 16 * distance - c ≤ 0 := by nlinarith
    linarith
  have hcosts := abs_le.mp hcost
  have hcrLower : c / 2 ≤ centerCost := by linarith
  have hcrUpper : centerCost ≤ 2 * c := by linarith
  have hUrpos : 0 < Ur := by linarith [hcenter.1]
  have hcScale : c ≤ 8 * A * b := by linarith [hcenter.1, heligible.2]
  have hAc := mul_le_mul_of_nonneg_left hcScale hA0.le
  have hAb : 0 ≤ A ^ 2 * b := mul_nonneg (sq_nonneg _) hb
  have hlower : Uq / (16 * A ^ 2) ≤ b := by
    apply (div_le_iff₀ (by positivity : 0 < 16 * A ^ 2)).2
    nlinarith [hquery.2]
  have hcenterScale := mul_le_mul_of_nonneg_left hcrUpper hA0.le
  have hqueryScale := mul_le_mul_of_nonneg_left hquery.1 (by positivity : 0 ≤ 4 * A)
  have hupper : b ≤ 4 * A * Uq := by nlinarith [heligible.1, hcenter.2]
  exact ⟨hdist, hUrpos.ne', hlower, hupper, by linarith [hquery.1]⟩

end EditApproximation

end OAI
