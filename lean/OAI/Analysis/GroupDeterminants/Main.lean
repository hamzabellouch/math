import OAI.Analysis.GroupDeterminants.CompanionTransfer
import OAI.RingTheory.DirectFiniteness.Main

namespace OAI

namespace GroupRingDeterminant

theorem companion_input : CompanionInput := by
  obtain ⟨K, hK, hKfin, hKchar, H, hH, hHfg, a, b, hab, hba⟩ :=
    KaplanskyCounterexample.main_theorem
  exact ⟨K, hK, Fintype.finite hKfin, hKchar, H, hH, hHfg, a, b, hab, hba⟩

theorem main : MainStatement := main_of_companion_input companion_input

end GroupRingDeterminant

end OAI
