import OAI.Combinatorics.Crossing.RoundCircleChords
import OAI.Combinatorics.Crossing.RoundDiskClearance

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem round_chord_subset_closed_disk (z a b : Plane) (r : ℝ)
    (ha : squaredLength (a-z)=r^2) (hb : squaredLength (b-z)=r^2) :
    segment ℝ a b ⊆ closedRoundDisk z r := by
  intro x hx
  rw [← Path.range_segment] at hx
  obtain ⟨t,rfl⟩ := hx
  change squaredLength (Path.segment a b t-z) ≤ r^2
  simp only [Path.segment_apply,AffineMap.lineMap_apply_module]
  have he : squaredLength (segmentPoint a b t.val-z)=
      (1-t.val)*squaredLength (a-z)+t.val*squaredLength (b-z)-
        t.val*(1-t.val)*squaredLength (b-a) := by
    dsimp [squaredLength,segmentPoint]
    ring
  change squaredLength (segmentPoint a b t.val-z) ≤ r^2
  rw [he,ha,hb]
  have hnon : 0 ≤ t.val*(1-t.val)*squaredLength (b-a) := by
    have ht0 := t.property.1
    have ht1 := sub_nonneg.mpr t.property.2
    dsimp [squaredLength]
    positivity
  linarith

theorem round_chord_boundary_endpoints (z a b x : Plane) (r : ℝ)
    (ha : squaredLength (a-z)=r^2) (hb : squaredLength (b-z)=r^2)
    (hx : x ∈ segment ℝ a b) (hboundary : squaredLength (x-z)=r^2) : x=a ∨ x=b := by
  by_cases hab : a=b
  · subst b
    exact Or.inl (by simpa only [segment_same,Set.mem_singleton_iff] using hx)
  · rw [← Path.range_segment] at hx
    obtain ⟨t,rfl⟩ := hx
    by_cases ht0 : t.val=0
    · left
      simp only [Path.segment_apply,AffineMap.lineMap_apply_module,ht0,sub_zero,one_smul,zero_smul,add_zero]
    · by_cases ht1 : t.val=1
      · right
        simp only [Path.segment_apply,AffineMap.lineMap_apply_module,ht1,sub_self,one_smul,zero_smul,zero_add]
      · have hstrict := round_chord_in_open_disk z a b r ha hb hab t.val
          ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩
        have hb' : squaredLength (segmentPoint a b t.val-z)=r^2 := by
          simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hboundary
        rw [hb'] at hstrict
        exact False.elim (lt_irrefl _ hstrict)

end Zarankiewicz

end

end OAI
