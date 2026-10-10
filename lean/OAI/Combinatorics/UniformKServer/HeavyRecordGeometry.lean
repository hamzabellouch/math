import Mathlib
import OAI.Combinatorics.UniformKServer.HeavySchedule
import OAI.Combinatorics.UniformKServer.HeavyRecords

namespace OAI

                                          
section

/-! The actual center-set projection and common-label properties of the
finite-slot heavy-ball update. -/
noncomputable section
namespace UniformKServer.HeavyRecords
open Finset
open scoped Classical
variable {X Λ : Type*} [MetricSpace X] {r : ℝ}

def centers (S : State X Λ r) : Finset X := S.present.image S.center

theorem centers_separated (S : State X Λ r) : HeavySchedule.Separated r (centers S) := by
  intro a ha b hb hn
  obtain ⟨i,hi,rfl⟩ := mem_image.mp ha
  obtain ⟨j,hj,rfl⟩ := mem_image.mp hb
  exact S.separated i hi j hj (fun he => hn (congrArg S.center he))

variable [Fintype Λ]

theorem centers_insert (S : State X Λ r) (hr : 0 ≤ r) (x : X) (R : ℝ)
    (hR : R ∈ Set.Icc (16*r) (20*r)) (fresh : Λ) (hf : fresh ∉ S.present) :
    centers (insert S hr x R hR fresh hf)=HeavyPilot.updateCenters r (centers S) x := by
  have hn := chosen_not_survivor S hr x R hR.2 fresh hf
  ext p
  simp only [centers,insert,mem_image,mem_insert,HeavyPilot.updateCenters,mem_filter]
  constructor
  · rintro ⟨l,hl,he⟩
    rcases hl with rfl | hl
    · left; simpa only [Function.update_self] using he.symm
    · have hlne : l ≠ chosen S x R fresh := fun he => hn (he ▸ hl)
      rw [Function.update_of_ne hlne] at he
      exact Or.inr ⟨⟨l,(mem_filter.mp hl).1,he⟩,he ▸ (mem_filter.mp hl).2⟩
  · rintro (rfl | ⟨⟨l,hl,he⟩,hd⟩)
    · exact ⟨chosen S p R fresh,Or.inl rfl,Function.update_self _ _ _⟩
    · have hs : l ∈ survivors S x := mem_filter.mpr ⟨hl,he ▸ hd⟩
      have hlne : l ≠ chosen S x R fresh := fun he => hn (he ▸ hs)
      exact ⟨l,Or.inr hs,by rwa [Function.update_of_ne hlne]⟩

theorem common_region_reused (S : State X Λ r) (hr : 0 ≤ r) (x : X) (R : ℝ)
    (hR : R ∈ Set.Icc (16*r) (20*r)) (fresh : Λ) (hf : fresh ∉ S.present)
    (p : X) (l : Λ) (hold : covers S l p) (hnew : dist x p ≤ R) :
    key (insert S hr x R hR fresh hf) p=key S p := by
  have he := chosen_of_intersects S hr x R hR.2 fresh l ⟨p,hold,hnew⟩
  rw [(key_some S hr p l).mpr hold]
  apply (key_some _ hr p l).mpr
  rw [←he]
  exact new_covers S hr x R hR fresh hf p hnew

theorem reused_distance (S : State X Λ r) (hr : 0 ≤ r) (x : X) (R : ℝ)
    (hR : R ∈ Set.Icc (16*r) (20*r)) (fresh : Λ) (hf : fresh ∉ S.present)
    (l : Λ) (ho : l ∈ S.present) (hn : l ∈ (insert S hr x R hR fresh hf).present) :
    dist (S.center l) ((insert S hr x R hR fresh hf).center l) ≤ 40*r := by
  by_cases he : l=chosen S x R fresh
  · subst l
    simp only [insert,Function.update_self]
    rcases chosen_cases S x R fresh with hh | ⟨he,_⟩
    · simpa only [dist_comm] using intersect_distance S x R _ hR.2 hh
    · exact (hf (he ▸ ho)).elim
  · simp only [insert,Function.update_of_ne he,dist_self]
    positivity

theorem unchanged_far (S : State X Λ r) (hr : 0 ≤ r) (x : X) (R : ℝ)
    (hR : R ∈ Set.Icc (16*r) (20*r)) (fresh : Λ) (hf : fresh ∉ S.present)
    (p : X) (hd : 120*r < dist x p) : key (insert S hr x R hR fresh hf) p=key S p := by
  have hnew : ¬ dist x p ≤ R := by linarith [hR.2]
  have hsurv (l : Λ) (hl : covers S l p) : l ∈ survivors S x := by
    refine mem_filter.mpr ⟨hl.1,?_⟩
    have ht := dist_triangle x (S.center l) p
    linarith [hl.2,(S.radius_bounds l hl.1).2]
  by_cases he : ∃ l, covers S l p
  · obtain ⟨l,hl⟩ := he
    rw [(key_some S hr p l).mpr hl]
    apply (key_some _ hr p l).mpr
    exact (covers_insert_iff S hr x R hR fresh hf l p).mpr (Or.inr ⟨hsurv l hl,hl⟩)
  · rw [(key_none S p).mpr he]
    apply (key_none _ p).mpr
    rintro ⟨l,hl⟩
    rcases (covers_insert_iff S hr x R hR fresh hf l p).mp hl with hh|hh
    · exact hnew hh.2
    · exact he ⟨l,hh.2⟩

variable [Fintype X]

theorem fresh_exists (S T : State X Λ r) (hr : 0 ≤ r)
    (hΛ : 2*Fintype.card X < Fintype.card Λ) : ∃ l : Λ, l ∉ S.present ∪ T.present := by
  have hc : (S.present ∪ T.present).card < Fintype.card Λ := by
    have hs := card_present S hr
    have ht := card_present T hr
    have hu := card_union_le S.present T.present
    omega
  by_contra h
  push Not at h
  have he : S.present ∪ T.present=univ := eq_univ_of_forall h
  rw [he,card_univ] at hc
  omega

end UniformKServer.HeavyRecords

end


end

end OAI
