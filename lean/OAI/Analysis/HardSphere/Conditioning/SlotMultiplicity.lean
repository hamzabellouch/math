import Mathlib
import OAI.Analysis.HardSphere.Geometry.PathSlots

namespace OAI

section

section
noncomputable section
open scoped Classical
namespace HardSphere.Comparison
open HardSphere.Lattice
variable {I V : Type*} [DecidableEq V]
lemma nearSlots_card_of_fiber (e : V→V→Prop) (c : I→V) (s t : Finset I)
    (B : ℕ) (hB : ∀v,(s.filter (fun i ↦ c i=v)).card≤B) :
    (nearSlots e c s t).card≤B*(encounterSet e (s.image c) (t.image c)).card := by
  have hm : (nearSlots e c s t).image c⊆
      (encounterSet e (s.image c) (t.image c)).image Prod.fst := by
    intro v hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨his,j,hjt,hij⟩ := (mem_nearSlots e c s t i).mp hi
    exact Finset.mem_image.mpr ⟨(c i,c j),(mem_encounterSet e _ _ _ _).mpr
      ⟨Finset.mem_image.mpr ⟨i,his,rfl⟩,Finset.mem_image.mpr ⟨j,hjt,rfl⟩,hij⟩,rfl⟩
  have hc : ((nearSlots e c s t).image c).card≤(encounterSet e (s.image c) (t.image c)).card :=
    (Finset.card_le_card hm).trans Finset.card_image_le
  calc
    _=∑v∈(nearSlots e c s t).image c,((nearSlots e c s t).filter (fun i ↦ c i=v)).card :=
      Finset.card_eq_sum_card_image c _
    _≤∑_v∈(nearSlots e c s t).image c,B := by
      apply Finset.sum_le_sum
      intro v _
      exact (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))).trans (hB v)
    _=((nearSlots e c s t).image c).card*B := by simp
    _≤B*(encounterSet e (s.image c) (t.image c)).card := by simpa only [Nat.mul_comm] using Nat.mul_le_mul_right B hc

variable {K : ℕ} {x y : DiscreteTorus K} {J : Type*}
lemma departure_anchor_injective (p : SimplePath x y) (anchor : J→DiscreteTorus K)
    (pick : Fin p.val.length→J)
    (hpick : ∀i,anchor (pick i)=pathVertexEmbedding p i.castSucc) :
    Set.InjOn anchor (Set.range pick) := by
  rintro a ⟨i,rfl⟩ b ⟨j,rfl⟩ hab
  rw [hpick i,hpick j] at hab
  have h := (pathVertexEmbedding p).injective hab
  have he : i=j := Fin.ext (congrArg (fun k : Fin (p.val.length+1) ↦ k.val) h)
  exact congrArg pick he

lemma routeSlots_start_fiber (p : SimplePath x y) (anchor : J→DiscreteTorus K)
    (pick : Fin p.val.length→J)
    (hpick : ∀i,anchor (pick i)=pathVertexEmbedding p i.castSucc) (v : DiscreteTorus K) :
    ((routeSlots (departureEmbedding p anchor pick hpick)).filter
      (fun i ↦ extendedAnchor anchor x i=v)).card≤2 := by
  let s := (routeSlots (departureEmbedding p anchor pick hpick)).filter
      (fun i ↦ extendedAnchor anchor x i=v)
  have hone : (s.erase none).card≤1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have hna := Finset.mem_erase.mp ha
    have hnb := Finset.mem_erase.mp hb
    obtain ⟨a,rfl⟩ := Option.ne_none_iff_exists'.mp hna.1
    obtain ⟨b,rfl⟩ := Option.ne_none_iff_exists'.mp hnb.1
    have has := Finset.mem_filter.mp hna.2
    have hbs := Finset.mem_filter.mp hnb.2
    rw [routeSlots_exact] at has hbs
    have hai : a∈Set.range pick := by
      rcases Finset.mem_insert.mp has.1 with h|h
      · contradiction
      · obtain ⟨i,_,he⟩ := Finset.mem_image.mp h
        exact ⟨i,Option.some.inj he⟩
    have hbi : b∈Set.range pick := by
      rcases Finset.mem_insert.mp hbs.1 with h|h
      · contradiction
      · obtain ⟨i,_,he⟩ := Finset.mem_image.mp h
        exact ⟨i,Option.some.inj he⟩
    exact congrArg some (departure_anchor_injective p anchor pick hpick hai hbi (has.2.trans hbs.2.symm))
  have hcard : s.card≤(s.erase none).card+1 := by
    have hin : s⊆insert none (s.erase none) := by intro a ha;by_cases h:a=none <;> simp_all
    exact (Finset.card_le_card hin).trans (Finset.card_insert_le _ _)
  exact hcard.trans (by omega)

end HardSphere.Comparison

end
end

section
noncomputable section
open scoped Classical
namespace HardSphere.Comparison
open HardSphere.Lattice
variable {K : ℕ} {x y : DiscreteTorus K} {J : Type*}
lemma routeSlots_start_sites (p : SimplePath x y) (anchor : J→DiscreteTorus K)
    (pick : Fin p.val.length→J)
    (hpick : ∀i,anchor (pick i)=pathVertexEmbedding p i.castSucc) :
    (routeSlots (departureEmbedding p anchor pick hpick)).image (extendedAnchor anchor x)⊆p.val.support.toFinset := by
  intro v hv
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
  rw [routeSlots_exact] at ha
  rcases Finset.mem_insert.mp ha with rfl|ha
  · exact List.mem_toFinset.mpr p.val.start_mem_support
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    change anchor (pick i)∈_
    rw [hpick i]
    exact List.mem_toFinset.mpr (p.val.getVert_mem_support i.val)

lemma second_primary_nearSlots_bound (R : ℕ) (p q : SimplePath x y) (anchor : J→DiscreteTorus K)
    (f : Fin p.val.length→J) (g : Fin q.val.length→J)
    (hf : ∀i,anchor (f i)=pathVertexEmbedding p i.castSucc)
    (hg : ∀i,anchor (g i)=pathVertexEmbedding q i.castSucc) :
    (nearSlots (torusNear K R) (extendedAnchor anchor x)
      (routeSlots (departureEmbedding p anchor f hf)) (routeSlots (departureEmbedding q anchor g hg))).card≤
      2*simpleEncounter R p q := by
  have h := nearSlots_card_of_fiber (torusNear K R) (extendedAnchor anchor x)
    (routeSlots (departureEmbedding p anchor f hf)) (routeSlots (departureEmbedding q anchor g hg))
    2 (routeSlots_start_fiber p anchor f hf)
  apply h.trans
  apply Nat.mul_le_mul_left
  apply Finset.card_le_card
  intro v hv
  obtain ⟨ha,hb,he⟩ := (mem_encounterSet _ _ _ _ _).mp hv
  exact (mem_encounterSet _ _ _ _ _).mpr
    ⟨routeSlots_start_sites p anchor f hf ha,routeSlots_start_sites q anchor g hg hb,he⟩

end HardSphere.Comparison

end
end

end

end OAI
