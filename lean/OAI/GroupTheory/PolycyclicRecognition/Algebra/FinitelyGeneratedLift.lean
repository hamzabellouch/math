import Mathlib.GroupTheory.Finiteness

namespace OAI

/-! # Finite generation lifts through a surjection

Only finitely many chosen lifts are needed. This does not assert that the
whole inverse image of a finitely generated subgroup is finitely generated.
-/

noncomputable section
namespace PolycyclicRecognition

theorem fg_subgroup_map {G A : Type*} [Group G] [Group A]
    {H : Subgroup G} (hH : H.FG) (q : G →* A) : (H.map q).FG := by
  obtain ⟨S, hS, hfin⟩ := (Subgroup.fg_iff H).mp hH
  refine (Subgroup.fg_iff _).mpr ⟨q '' S, ?_, hfin.image q⟩
  rw [← MonoidHom.map_closure, hS]

theorem exists_fg_subgroup_surjective {G A : Type*} [Group G] [Group A]
    [Group.FG A] (q : G →* A) (hq : Function.Surjective q) :
    ∃ H : Subgroup G, H.FG ∧ Function.Surjective (q.comp H.subtype) := by
  obtain ⟨S, hS, hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG A)
  choose s hs using hq
  let H := Subgroup.closure (s '' S)
  have himage : q '' (s '' S) = S := by
    ext a
    constructor
    · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      simpa only [hs] using hb
    · intro ha
      exact ⟨s a, ⟨a, ha, rfl⟩, hs a⟩
  have hmap : H.map q = ⊤ := by
    change (Subgroup.closure (s '' S)).map q = ⊤
    rw [MonoidHom.map_closure, himage, hS]
  refine ⟨H, (Subgroup.fg_iff H).mpr ⟨s '' S, rfl, hfin.image s⟩, ?_⟩
  intro a
  have ha : a ∈ H.map q := by rw [hmap]; trivial
  obtain ⟨g, hg, hga⟩ := ha
  exact ⟨⟨g, hg⟩, hga⟩

end PolycyclicRecognition

end

end OAI
