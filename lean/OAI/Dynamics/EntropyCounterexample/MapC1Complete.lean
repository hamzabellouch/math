import OAI.Dynamics.EntropyCounterexample.MapC1
import OAI.Dynamics.EntropyCounterexample.MapMainRegularity
import OAI.Dynamics.EntropyCounterexample.MapInputRegularity
import OAI.Dynamics.EntropyCounterexample.RealizedRegisterRegularity

namespace OAI

noncomputable section

namespace Problem340.Construction

theorem exists_threshold_isC1SelfMap_realizedMap :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (L : ℝ) (hL : 2 < L), B < L →
      IsC1SelfMap 3 (realizedMap L hL) := by
  obtain ⟨B, hB, hinput⟩ := exists_registerInput_hasLocalC1Extension
  refine ⟨B, hB, ?_⟩
  intro L hL hBL
  apply isC1SelfMap_realizedMap_of_sphere_components L hL
    (realizedMap_main_hasLocalC1Extension L hL)
  intro i
  exact realizedMap_register_hasLocalC1Extension L hL i (hinput L hL hBL i)

theorem exists_isC1SelfMap_realizedMap :
    ∃ (L : ℝ) (hL : 2 < L), IsC1SelfMap 3 (realizedMap L hL) := by
  obtain ⟨B, hB, hreg⟩ := exists_threshold_isC1SelfMap_realizedMap
  have hL : 2 < B + 3 := by linarith
  exact ⟨B + 3, hL, hreg (B + 3) hL (by linarith)⟩

end Problem340.Construction

end

end OAI
