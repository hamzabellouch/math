import Mathlib
import OAI.Computability.VertexCover.Reduction.NormAttainedSupport
import OAI.Computability.VertexCover.Reduction.PairSeedFiberCard

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover

def ListHit (Φ : LabelCover) {d : ℕ} (L : Φ.PrivateLists d)
    (seed : Φ.Seeds d) (I : Finset (Φ.Coordinate d)) (j : Fin d) : Prop :=
  ∃ a ∈ L (Φ.query seed j), (⟨Φ.query seed j, a⟩ : Φ.Coordinate d) ∈ I

noncomputable def hitPositions (Φ : LabelCover) {d : ℕ} (L : Φ.PrivateLists d)
    (seed : Φ.Seeds d) (I : Finset (Φ.Coordinate d)) (J : Finset (Fin d)) : Finset (Fin d) := by
  classical
  exact J.filter (Φ.ListHit L seed I)

noncomputable def pairEvents (Φ : LabelCover) {d : ℕ} (L : Φ.PrivateLists d)
    (seed : Φ.Seeds d) (J : Finset (Fin d)) : Finset (PositionPair d) := by
  classical
  exact Finset.univ.filter (fun e => e.1.1 ∈ J ∧ e.1.2 ∈ J ∧ Φ.PairSeedHit L seed e)

theorem pairSeedHit_of_hits (Φ : LabelCover) {d : ℕ} (L : Φ.PrivateLists d)
    (seed : Φ.Seeds d) {I : Finset (Φ.Coordinate d)} (hI : Φ.Compatible I)
    (e : PositionPair d) (hj : Φ.ListHit L seed I e.1.1)
    (hk : Φ.ListHit L seed I e.1.2) : Φ.PairSeedHit L seed e := by
  classical
  obtain ⟨a, haL, haI⟩ := hj
  obtain ⟨b, hbL, hbI⟩ := hk
  refine ⟨a, haL, b, hbL, Φ.compatible_mono hI ?_⟩
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact haI
  · exact hbI

theorem hitPositions_card_le (Φ : LabelCover) {d : ℕ} (L : Φ.PrivateLists d)
    (seed : Φ.Seeds d) (I : Finset (Φ.Coordinate d)) (hI : Φ.Compatible I)
    (J : Finset (Fin d)) :
    (Φ.hitPositions L seed I J).card ≤ 1 + (Φ.pairEvents L seed J).card := by
  classical
  let A := Φ.hitPositions L seed I J
  by_cases hA : A.Nonempty
  · let j := A.min' hA
    have hj : j ∈ A := Finset.min'_mem _ _
    have keep : ∀ k : ↥(A.erase j), j < k.1 := by
      intro k
      have hk := Finset.mem_erase.mp k.2
      exact lt_of_le_of_ne (Finset.min'_le A k.1 hk.2) (Ne.symm hk.1)
    let inject : ↥(A.erase j) → ↥(Φ.pairEvents L seed J) := fun k =>
      ⟨⟨(j, k.1), keep k⟩, by
        have hmj := Finset.mem_filter.mp hj
        have hmk := Finset.mem_filter.mp (Finset.mem_erase.mp k.2).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmj.1, hmk.1,
          Φ.pairSeedHit_of_hits L seed hI _ hmj.2 hmk.2⟩⟩
    have hinj : Function.Injective inject := by
      intro k l h
      apply Subtype.ext
      exact congrArg (fun e : ↥(Φ.pairEvents L seed J) => e.1.1.2) h
    have hcard := Fintype.card_le_of_injective inject hinj
    simp only [Fintype.card_coe] at hcard
    have herase := Finset.card_erase_add_one hj
    change A.card ≤ _
    omega
  · have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    change A.card ≤ _
    simp [he]

noncomputable def listHitMaximum (Φ : LabelCover) {d : ℕ} (L : Φ.PrivateLists d)
    (seed : Φ.Seeds d) (J : Finset (Fin d)) : ℕ :=
  (Φ.compatibleSelections d).sup (fun I => (Φ.hitPositions L seed I J).card)

theorem listHitMaximum_le (Φ : LabelCover) {d : ℕ} (L : Φ.PrivateLists d)
    (seed : Φ.Seeds d) (J : Finset (Fin d)) :
    Φ.listHitMaximum L seed J ≤ 1 + (Φ.pairEvents L seed J).card := by
  classical
  apply Finset.sup_le
  intro I hI
  exact Φ.hitPositions_card_le L seed I ((Φ.mem_compatibleSelections I).mp hI) J

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
