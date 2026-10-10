import OAI.MeasureTheory.Falconer.Angular.QuantitativeCaps
import OAI.MeasureTheory.Falconer.Estimates.NonstationaryPower

namespace OAI

/-!
# The polynomial cost of all cap pairs

The slightly weaker ambient-dimensional cap count suffices here, because
each integration by parts supplies a fixed positive power gain.
-/

namespace Falconer

theorem graph_cap_inverse_bound {R c₀ σ a p : ℝ}
    (hR : 1 ≤ R) (hc₀ : 0 < c₀) (hσ : 0 ≤ σ) (hp : p-a ≤ 1) :
    (min c₀ (R^(a-p+10*σ)))⁻¹ ≤ c₀⁻¹+R := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  by_cases hc : c₀ ≤ R^(a-p+10*σ)
  · rw [min_eq_left hc]
    linarith
  · rw [min_eq_right (le_of_not_ge hc),← Real.rpow_neg hR0.le]
    have hh : R^(-(a-p+10*σ)) ≤ R := by
      conv_rhs => rw [← Real.rpow_one R]
      exact Real.rpow_le_rpow_of_exponent_le hR (by linarith)
    linarith [inv_pos.mpr hc₀]

theorem graph_cap_count_polynomial {d : ℕ} {R c₀ σ a p : ℝ}
    (hR : 1 ≤ R) (hc₀ : 0 < c₀) (hσ : 0 ≤ σ) (hp : p-a ≤ 1)
    (S : Finset (Sphere d))
    (hcard : (S.card : ℝ) ≤ (4/(min c₀ (R^(a-p+10*σ)))+1)^d) :
    (S.card : ℝ) ≤ (5+4*c₀⁻¹)^d*R^d := by
  have hi := graph_cap_inverse_bound hR hc₀ hσ hp
  have hpos : 0 ≤ c₀⁻¹ := (inv_pos.mpr hc₀).le
  have hbase : 4/(min c₀ (R^(a-p+10*σ)))+1 ≤ (5+4*c₀⁻¹)*R := by
    rw [div_eq_mul_inv]
    nlinarith
  apply hcard.trans
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by positivity) hbase d

end Falconer

end OAI
