import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Abelianization.Defs
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FinitelyGeneratedLift

namespace OAI

/-! # Generators lift from the abelianization of a nilpotent group

This does not require the group or the subgroup of lifts to be finitely
generated. Central-quotient induction proves the generation statement.
-/

namespace PolycyclicRecognition
variable {G : Type} [Group G] [Group.IsNilpotent G]

theorem nilpotent_eq_top_of_sup_commutator (H : Subgroup G)
    (hH : H ⊔ commutator G = ⊤) : H = ⊤ := by
  apply Group.nilpotent_center_quotient_ind G
    (P := fun K _ _ => ∀ L : Subgroup K, L ⊔ commutator K = ⊤ → L = ⊤) ?_ ?_ H hH
  · intro K _ _ L _
    exact Subsingleton.elim _ _
  · intro K _ _ ih L hL
    let Z := Subgroup.center K
    let q := QuotientGroup.mk' Z
    have hmap : L.map q ⊔ commutator (K ⧸ Z) = ⊤ := by
      have h := congrArg (Subgroup.map q) hL
      simpa only [Subgroup.map_sup, Subgroup.map_commutator,
        q.range_eq_top_of_surjective (QuotientGroup.mk'_surjective Z), Subgroup.map_top,
        _root_.commutator_def] using h
    have hqL := ih (L.map q) hmap
    have hLZ : L ⊔ Z = ⊤ := by
      have h := congrArg (Subgroup.comap q) hqL
      rw [Subgroup.comap_map_eq, Subgroup.comap_top] at h
      change L ⊔ (QuotientGroup.mk' Z).ker = ⊤ at h
      simpa only [QuotientGroup.ker_mk'] using h
    let : L.Normal := Subgroup.normalizer_eq_top_iff.mp (by
      apply top_unique
      rw [← hLZ]
      exact sup_le L.le_normalizer (Subgroup.center_le_normalizer (G := K) (L : Set K)))
    have hcomm : commutator K ≤ L :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hLZ inferInstance
    rw [sup_eq_left.mpr hcomm] at hL
    exact hL

theorem nilpotent_finitelyGenerated_of_abelianization [Group.FG (Abelianization G)] :
    Group.FG G := by
  obtain ⟨H, hHfg, hHsurj⟩ := exists_fg_subgroup_surjective (Abelianization.of (G := G))
    (QuotientGroup.mk'_surjective (commutator G))
  have hmap : H.map (Abelianization.of (G := G)) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨g, hg⟩ := hHsurj x
    exact ⟨g, g.property, hg⟩
  have hsup : H ⊔ commutator G = ⊤ := by
    have h := congrArg (Subgroup.comap (Abelianization.of (G := G))) hmap
    simpa only [Subgroup.comap_map_eq, Abelianization.ker_of, Subgroup.comap_top] using h
  have htop := nilpotent_eq_top_of_sup_commutator H hsup
  exact Group.fg_def.mpr (htop ▸ hHfg)

end PolycyclicRecognition

end OAI
