import OAI.GroupTheory.PolycyclicRecognition.Algebra.AscendingRefinement
import OAI.GroupTheory.PolycyclicRecognition.Algebra.DirectedLowerCentral

namespace OAI

/-! # Nilpotence in an increasing union of automorphic images -/

noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G] (α : MulAut G) (K : Subgroup G)

theorem nilpotent_automorphism_iSup (hK : K.map α.toMonoidHom ≤ K)
    [Group.IsNilpotent K] :
    Group.IsNilpotent (⨆ n, automorphismStage α K n : Subgroup G) := by
  obtain ⟨c, hc⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries K).mp inferInstance
  have hm := automorphismStage_monotone α K hK
  have hne : (Set.range (automorphismStage α K)).Nonempty := ⟨_, ⟨0, rfl⟩⟩
  have hdir : DirectedOn (· ≤ ·) (Set.range (automorphismStage α K)) := by
    rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩
    exact ⟨_, ⟨max n m, rfl⟩, hm (le_max_left _ _), hm (le_max_right _ _)⟩
  apply (Subgroup.isNilpotent_iff_lowerCentralSeries _).mpr
  refine ⟨c, ?_⟩
  rw [← sSup_range]
  apply sSup_lowerCentralSeries_eq_bot _ hne hdir c
  rintro _ ⟨n, rfl⟩
  change (K.map ((α⁻¹) ^ n).toMonoidHom).lowerCentralSeries c = ⊥
  rw [← Subgroup.map_lowerCentralSeries, hc, Subgroup.map_bot]

end PolycyclicRecognition

end

end OAI
