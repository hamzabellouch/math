import Mathlib
import OAI.Probability.CriticalPercolation.Gluing.SlotContour
import OAI.Probability.CriticalPercolation.Gluing.CorridorSeparation

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.Corridor
open Boundary

def slotSite (n : ℕ) : Site := ((Nat.unpair n).1,(Nat.unpair n).2)

lemma slotSite_quadrant (n : ℕ) : quadrant (slotSite n) := by
  exact ⟨Int.natCast_nonneg _,Int.natCast_nonneg _⟩

lemma gridSlot_slotSite (n : ℕ) : gridSlot (slotSite n)=n := by
  simp [gridSlot,slotSite]

lemma slotSite_gridSlot (v : Site) (hv : quadrant v) : slotSite (gridSlot v)=v := by
  apply gridSlot_injective (slotSite_quadrant _) hv
  exact gridSlot_slotSite _

lemma slotSite_zero : slotSite 0=(0,0) := rfl

lemma parent_slot_lt (e : Edge) (h : quadrant (source e)) :
    gridSlot (source e)<gridSlot (target e) := by
  obtain ⟨v,b⟩ := e
  cases b with
  | true => exact gridSlot_east v h
  | false => exact gridSlot_north v h

lemma target_quadrant (e : Edge) (h : quadrant (source e)) : quadrant (target e) := by
  obtain ⟨⟨a,b⟩,s⟩ := e
  change 0≤a ∧ 0≤b at h
  cases s <;> dsimp [target,quadrant] <;> omega

def incoming (n : ℕ) (S : Finset Site) : Option Edge :=
  if (slotSite n-(1,0))∈S then some (slotSite n-(1,0),true)
  else if (slotSite n-(0,1))∈S then some (slotSite n-(0,1),false) else none

lemma incoming_source {n : ℕ} {S : Finset Site} {e : Edge}
    (h : incoming n S=some e) : source e∈S := by
  unfold incoming at h
  split_ifs at h with hw hn
  · have he := Option.some.inj h
    subst e
    exact hw
  · have he := Option.some.inj h
    subst e
    exact hn

lemma incoming_target {n : ℕ} {S : Finset Site} {e : Edge}
    (h : incoming n S=some e) : target e=slotSite n := by
  unfold incoming at h
  split_ifs at h with hw hn
  · have he := Option.some.inj h
    subst e
    simp [target]
  · have he := Option.some.inj h
    subst e
    simp [target]

lemma incoming_exists (n : ℕ) (S : Finset Site)
    (h : ∃ y∈S, slotSite n=y+(1,0) ∨ slotSite n=y+(0,1)) :
    ∃ e, incoming n S=some e := by
  unfold incoming
  split_ifs with hw hn
  · exact ⟨_,rfl⟩
  · exact ⟨_,rfl⟩
  · obtain ⟨y,hy,he|he⟩ := h
    · exact (hw (by rwa [he,add_sub_cancel_right])).elim
    · exact (hn (by rwa [he,add_sub_cancel_right])).elim

structure GrowthState where
  good : Finset Site
  seen : Finset Edge

def GrowthState.initial : GrowthState := ⟨{(0,0)},∅⟩

def GrowthState.advance (n : ℕ) (S : GrowthState) (b : Bool) : GrowthState where
  good := if (incoming n S.good).isSome ∧ b=true then insert (slotSite n) S.good else S.good
  seen := S.seen∪(incoming n S.good).toFinset

lemma GrowthState.good_mono (n : ℕ) (S : GrowthState) (b : Bool) :
    S.good⊆(S.advance n b).good := by
  dsimp [advance]
  split_ifs <;> intro v hv
  · exact Finset.mem_insert_of_mem hv
  · exact hv

lemma GrowthState.seen_mono (n : ℕ) (S : GrowthState) (b : Bool) :
    S.seen⊆(S.advance n b).seen := Finset.subset_union_left

def GrowthState.Valid (n : ℕ) (S : GrowthState) : Prop :=
  (0,0)∈S.good ∧
  (∀ v∈S.good, quadrant v ∧ (v=(0,0) ∨ gridSlot v<n)) ∧
  (∀ e∈S.seen, source e∈S.good ∧ gridSlot (target e)<n)

lemma GrowthState.initial_valid : GrowthState.initial.Valid 0 := by
  refine ⟨by simp [initial],?_,by simp [initial]⟩
  intro v hv
  have he : v=(0,0) := by simpa [initial] using hv
  subst v
  exact ⟨by norm_num [quadrant],Or.inl rfl⟩

lemma GrowthState.advance_valid (n : ℕ) (S : GrowthState) (b : Bool)
    (h : S.Valid n) : (S.advance n b).Valid (n+1) := by
  refine ⟨S.good_mono n b h.1,?_,?_⟩
  · intro v hv
    change v∈(if (incoming n S.good).isSome ∧ b=true then insert (slotSite n) S.good else S.good) at hv
    split_ifs at hv with ha
    · rcases Finset.mem_insert.mp hv with rfl|hv
      · exact ⟨slotSite_quadrant n,Or.inr (by rw [gridSlot_slotSite]; omega)⟩
      · exact ⟨(h.2.1 v hv).1,(h.2.1 v hv).2.imp_right (fun hh => by omega)⟩
    · exact ⟨(h.2.1 v hv).1,(h.2.1 v hv).2.imp_right (fun hh => by omega)⟩
  · intro e he
    rcases Finset.mem_union.mp he with he|he
    · exact ⟨S.good_mono n b (h.2.2 e he).1,by have hh := (h.2.2 e he).2; omega⟩
    · have hei : incoming n S.good=some e := by simpa using he
      exact ⟨S.good_mono n b (incoming_source hei),by rw [incoming_target hei,gridSlot_slotSite]; omega⟩

lemma GrowthState.seen_intersection (n : ℕ) (S : GrowthState) (h : S.Valid n)
    {e : Edge} (ht : n ≤ gridSlot (target e)) :
    e∉S.seen ∧ ∀ f∈S.seen, endpoints f∩endpoints e⊆{source e} := by
  refine ⟨fun hei => (Nat.not_lt_of_ge ht) (h.2.2 e hei).2,?_⟩
  intro f hf v hv
  have hfs := (h.2.1 (source f) (h.2.2 f hf).1).1
  have hft := (h.2.2 f hf).2
  have hfst := parent_slot_lt f hfs
  rcases hv.1 with rfl|hvf <;> rcases hv.2 with hve|hve
  · exact hve
  · have heq : source f=target e := hve
    rw [heq] at hfst
    omega
  · exact hve
  · have heq : target f=target e := hvf.symm.trans hve
    rw [heq] at hft
    omega

def GrowthState.Covered (S : GrowthState) : Prop :=
  ∀ v∈S.good, v=(0,0) ∨ ∃ e∈S.seen, target e=v

lemma GrowthState.initial_covered : GrowthState.initial.Covered := by
  intro v hv
  exact Or.inl (by simpa [initial] using hv)

lemma GrowthState.advance_covered (n : ℕ) (S : GrowthState) (b : Bool)
    (h : S.Covered) : (S.advance n b).Covered := by
  intro v hv
  change v∈(if (incoming n S.good).isSome ∧ b=true then insert (slotSite n) S.good else S.good) at hv
  have hold : ∀ v∈S.good, v=(0,0) ∨ ∃ e∈(S.advance n b).seen, target e=v := by
    intro v hv
    rcases h v hv with hv|⟨e,he,hv⟩
    · exact Or.inl hv
    · exact Or.inr ⟨e,S.seen_mono n b he,hv⟩
  split_ifs at hv with ha
  · rcases Finset.mem_insert.mp hv with rfl|hv
    · obtain ⟨e,he⟩ := Option.isSome_iff_exists.mp ha.1
      exact Or.inr ⟨e,Finset.mem_union.mpr (Or.inr (by simp [he])),incoming_target he⟩
    · exact hold v hv
  · exact hold v hv

lemma GrowthState.active_pos (n : ℕ) (S : GrowthState) (h : S.Valid n)
    {e : Edge} (he : incoming n S.good=some e) : 0<n := by
  have hq := (h.2.1 _ (incoming_source he)).1
  have hp := parent_slot_lt e hq
  rw [incoming_target he,gridSlot_slotSite] at hp
  omega

lemma GrowthState.outgoing_nonincident (n : ℕ) (S : GrowthState) (h : S.Valid n)
    {e : Edge} (he : source e=slotSite n) {f : Edge} (hf : f∈S.seen) :
    Disjoint (endpoints f) (endpoints e) := by
  have hq := (h.2.1 _ (h.2.2 f hf).1).1
  have hf1 := parent_slot_lt f hq
  have hf2 := (h.2.2 f hf).2
  have he1 := parent_slot_lt e (he ▸ slotSite_quadrant n)
  have he2 : gridSlot (source e)=n := by rw [he,gridSlot_slotSite]
  apply Set.disjoint_left.mpr
  intro v hv hw
  rcases hv with hv|hv <;> rcases hw with hw|hw
  · have hh : source f=source e := hv.symm.trans hw
    rw [hh,he2] at hf1
    omega
  · have hh : source f=target e := hv.symm.trans hw
    rw [hh] at hf1
    omega
  · have hh : target f=source e := hv.symm.trans hw
    rw [hh,he2] at hf2
    omega
  · have hh : target f=target e := hv.symm.trans hw
    rw [hh] at hf2
    omega

end CriticalPercolation.Corridor
end
end
end

end OAI
