import OAI.Analysis.PlanarPacking.ResidualTail
import OAI.Analysis.PlanarPacking.ResidualFinite
import OAI.Analysis.PlanarPacking.JetError

namespace OAI

/-!
# Bounds for the exact cardinal coefficients

The interpolation residual and inverse estimates give explicit bounds for the exact cardinal coefficient families.
-/

namespace SharpPlanar
lemma coefficient_error_bound (a : Bool) : ‖coefficientError a‖ < (3:ℝ)/10^5 := by
  have hh:=pair_error_estimate
    (fun a => (residual_finite_bound a).le) residual_tail_bound a
  norm_num at hh ⊢
  linarith
lemma exact_coeff_mass (a : Bool) :
    |(exactData a).c₀|+|(exactData a).d₀|+‖(exactData a).x‖ < (23:ℝ)/10 := by
  have hfix:=table_exact_fixed a
  have htab:=table_coeff_mass a
  have he:=coefficient_error_bound a
  rw [← hfix.2.1,← hfix.2.2, exactData_x]
  have hx : exactList a=tableList a-coefficientError a := by
    unfold coefficientError; abel
  rw [hx]
  have hn:=norm_sub_le (tableList a) (coefficientError a)
  change |(tableData a).c₀|+|(tableData a).d₀|+‖tableList a‖<_ at htab
  linarith
lemma exact_constant_bound (a : Bool) : |(exactData a).C| ≤ (17:ℝ)/1000 := by
  rw [← (table_exact_fixed a).1]
  exact table_constant_bound a
end SharpPlanar

end OAI
