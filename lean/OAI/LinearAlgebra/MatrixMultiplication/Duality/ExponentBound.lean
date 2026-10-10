import OAI.LinearAlgebra.MatrixMultiplication.Duality.FamilyConstruction
import OAI.LinearAlgebra.MatrixMultiplication.Duality.WitnessRealization
import OAI.LinearAlgebra.MatrixMultiplication.Duality.WitnessRates

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualWitnessRealization

@[simp] theorem pairRate_law (pair : ReaderPair) :
    DualFiniteRealization.pairRate hierarchy DualWitness.law pair = DualWitness.rate pair := rfl

end MatrixMultiplication.DualWitnessRealization

namespace MatrixMultiplication.DualExponentBound

open DualWitnessRealization

theorem fixedAspect_actual_families :
    ∀ ε : ℝ, 0 < ε → Nonempty (ActualFamily fixedAspect (2 + ε)) := by
  apply DualFiniteRealization.arbitrarily_close_families_of_exact_incident
    hierarchy hierarchy_complete DualWitness.law approximation
    (pow_pos (by decide : 0 < (2 : ℕ)) 288) source_supported source_unit
    source_log_positive
  · rw [pairRate_law, pairRate_law, source_log]
    exact DualWitnessRates.incident_rate
  · rw [pairRate_law, pairRate_law, pairRate_law,
      DualWitnessRates.incident_rate, DualWitnessRates.hidden_rate]
    have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hgap := (lt_div_iff₀ hlog).mp fixedAspect_lt_dual_aspect
    change fixedAspect * Real.log 2 < 2 * DualWitness.hiddenRate at hgap
    nlinarith

theorem fixedAspect_omega_eq_two : Arithmetic.rectangularOmega ℂ fixedAspect = 2 :=
  omega_eq_two_of_arbitrarily_close_families fixedAspect_mem_unit.1 fixedAspect_actual_families

theorem alpha_gt : (93 : ℝ) / 200 < Arithmetic.complexAlpha :=
  alpha_gt_target_of_arbitrarily_close_families fixedAspect_actual_families

end MatrixMultiplication.DualExponentBound

end

end OAI
