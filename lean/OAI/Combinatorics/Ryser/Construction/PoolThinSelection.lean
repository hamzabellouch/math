import OAI.Combinatorics.Ryser.Construction.PoolThinProbability
import OAI.Combinatorics.Ryser.Construction.GroupBounds
import OAI.Combinatorics.Ryser.Construction.FiniteOutsideAction
import OAI.Combinatorics.Ryser.Construction.CoordinateCompatibility

namespace OAI

noncomputable section
open scoped Classical

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F] [Fintype k] [Fintype F]
variable [DecidableEq k] [DecidableEq F] {K : ℕ}

theorem offPencilThin_of_groupPoolThin
    (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (pool : ConfigurationGroup σ → Fin K → Point F)
    (choice : ConfigurationGroup σ → Fin K)
    (Y : Finset (Point k)) (X : Finset (Point F))
    (hthin : PoolThin (groupPoints σ u v huv) (groupAltered σ u v huv) pool)
    (p : Point F) :
    OffPencilThin
      (placedConfiguration σ (groupPlacement σ u v huv)
        (fun i => pool i (choice i)) Y X) p := by
  classical
  let data := placedConfiguration σ (groupPlacement σ u v huv)
    (fun i => pool i (choice i)) Y X
  intro ell hp
  apply (Finset.card_le_card ?_).trans (hthin p ell hp)
  intro i hi
  obtain ⟨w, hw, hinc, hdir⟩ := (mem_offPencilGroups data p ell i).mp hi
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, choice i, ?_⟩
  refine ⟨(groupPlacement σ u v huv i).apply (mapPoint σ w), ?_,
    joinDirection p (data.base i w), hdir, hinc, ?_⟩
  · exact Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩
  · exact incidence_joinLine_right p (data.base i w)

end RyserCoveringCounterexample.Construction

end

end OAI
