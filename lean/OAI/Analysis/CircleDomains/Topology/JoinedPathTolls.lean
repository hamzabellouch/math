import OAI.Analysis.CircleDomains.Topology.JoinedPaths
import OAI.Analysis.CircleDomains.Selection.CountableConcatenationTolls

namespace OAI

/-! The two endpoint tolls remain omitted after joining at a point with
zero dust weight. -/

open Set Function
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem joinedPath_interior_toll (γ δ : C(PathTime, X)) (h : γ ⊤ = δ ⊥)
    (m : X → ℝ≥0∞) (hm : m (γ ⊤) = 0) :
    timeToll (joinedPath γ δ h) (Ioo (⊥ : PathTime) ⊤) m =
      timeToll γ (Ioo (⊥ : PathTime) ⊤) m + timeToll δ (Ioo (⊥ : PathTime) ⊤) m := by
  let c := collarTime 1
  have hmid : joinedPath γ δ h c = γ ⊤ := by
    simpa only [affinePathTime_one] using joinedPath_first γ δ h ⊤
  have hsplit : timeToll (joinedPath γ δ h) (Ioo (⊥ : PathTime) ⊤) m =
      timeToll (joinedPath γ δ h) (Ioo ⊥ c ∪ Ioo c ⊤) m := by
    apply timeToll_eq_of_zero_difference
    · rintro t (ht | ht)
      · exact ⟨ht.1, ht.2.trans_le le_top⟩
      · exact ⟨lt_of_le_of_lt bot_le ht.1, ht.2⟩
    · intro t ht
      have he : t = c := by
        rcases lt_trichotomy t c with hlt | he | hgt
        · exact (ht.2 (Or.inl ⟨ht.1.1, hlt⟩)).elim
        · exact he
        · exact (ht.2 (Or.inr ⟨hgt, ht.1.2⟩)).elim
      rw [he, hmid, hm]
  rw [hsplit, timeToll_union _ _ (by
    apply disjoint_left.mpr
    intro t ht hs
    exact ht.2.not_gt hs.1)]
  congr 1
  · rw [← interiorToll_affine (joinedPath γ δ h) m (collarTime_pos 1)]
    apply timeToll_congr_path
    intro t _
    exact joinedPath_first γ δ h t
  · have hc : c < (⊤ : PathTime) := by
      exact (collarTime_zero ▸ collarTime_strictAnti (by omega : 0 < 1))
    rw [← interiorToll_affine (joinedPath γ δ h) m hc]
    apply timeToll_congr_path
    intro t _
    exact joinedPath_second γ δ h t

end CircleDomainRigidity

end

end OAI
