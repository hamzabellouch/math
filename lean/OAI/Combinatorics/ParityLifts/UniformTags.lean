import OAI.Combinatorics.ParityLifts.UniformRoles

namespace OAI

namespace ParityWL.Complexity
open scoped BigOperators
open Classical

lemma bit_zero_or_one (x : Bit) : x=0 ∨ x=1 := by
  have hx := ZMod.val_lt x
  have he := ZMod.natCast_zmod_val x
  have hv : x.val=0 ∨ x.val=1 := by omega
  rcases hv with hv | hv
  · left; simpa [hv] using he.symm
  · right; simpa [hv] using he.symm

lemma sum_indicator_list {α β R : Type} [Fintype α] [BEq β] [LawfulBEq β]
    [AddCommMonoidWithOne R] (f : α → β) (hf : Function.Injective f)
    (s : List β) (hs : s.Nodup) (hc : ∀ x∈s, ∃ a,f a=x) :
    ∑ a : α, (if f a∈s then (1 : R) else 0) = (s.length : R) := by
  classical
  rw [Finset.sum_boole]
  congr 1
  let e : α ↪ β := ⟨f,hf⟩
  have he : (Finset.univ.filter (fun a => f a∈s)).map e=s.toFinset := by
    ext x
    simp only [Finset.mem_map,Finset.mem_filter,Finset.mem_univ,true_and,List.mem_toFinset]
    constructor
    · rintro ⟨a,ha,rfl⟩; exact ha
    · intro hx
      obtain ⟨a,ha⟩ := hc x hx
      exact ⟨a,ha ▸ hx,ha⟩
  rw [←Finset.card_map e,he,List.toFinset_card_of_nodup hs]

lemma rawTag_sum {t : ℕ} (a : TemplateVertex t) (s : List RawRole)
    (hs : s.Sublist (rawNeighbors t (rawRole a))) :
    ∑ v : (template t).neighborSet a, (if rawRole v.val∈s then (1 : Bit) else 0) = (s.length : Bit) := by
  classical
  apply sum_indicator_list _ (by
    intro v w h
    exact Subtype.ext ((rawRole_injective t) h)) s (List.Nodup.sublist hs (rawNeighbors_nodup t _))
  intro r hr
  have h := (mem_rawNeighbors t _ r).mp (hs.subset hr)
  let v := roleDecode ⟨r,h.1⟩
  have hv : rawRole v=r := rawRole_roleDecode ⟨r,h.1⟩
  have ha : (template t).Adj a v := (rawAdjacent_iff a v).mp (by simpa only [hv] using h.2)
  exact ⟨⟨v,ha⟩,hv⟩

noncomputable def tagOnes {t : ℕ} (a : TemplateVertex t) (z : (template t).neighborSet a → Bit) : List RawRole := by
  classical
  exact (rawNeighbors t (rawRole a)).filter (fun r => decide (∃ v : (template t).neighborSet a, rawRole v.val=r ∧ z v=1))

lemma tagOnes_sublist {t : ℕ} (a : TemplateVertex t) (z : (template t).neighborSet a → Bit) :
    (tagOnes a z).Sublist (rawNeighbors t (rawRole a)) := List.filter_sublist

lemma mem_tagOnes {t : ℕ} (a : TemplateVertex t) (z : (template t).neighborSet a → Bit)
    (v : (template t).neighborSet a) : rawRole v.val∈tagOnes a z ↔ z v=1 := by
  classical
  simp only [tagOnes,List.mem_filter,decide_eq_true_eq]
  constructor
  · rintro ⟨_,w,hw,hz⟩
    have he : w=v := Subtype.ext ((rawRole_injective t) hw)
    simpa only [he] using hz
  · intro hz
    exact ⟨(mem_rawNeighbors t _ _).mpr ⟨rawRole_valid v.val,(rawAdjacent_iff a v.val).mpr v.property⟩,
      v,rfl,hz⟩

lemma tagOnes_sum {t : ℕ} (a : TemplateVertex t) (z : (template t).neighborSet a → Bit) :
    ((tagOnes a z).length : Bit)=∑ v,z v := by
  classical
  rw [←rawTag_sum a _ (tagOnes_sublist a z)]
  apply Finset.sum_congr rfl
  intro v _
  rcases bit_zero_or_one (z v) with hz | hz <;> simp [mem_tagOnes,hz]

abbrev RawTag := RawRole × List RawRole

def rawCharge (odd : Bool) (a : RawRole) : ℕ := if odd && decide (a=(0,0,0)) then 1 else 0

def tagCharge (t : ℕ) (odd : Bool) : TemplateVertex t → Bit :=
  fun a => (rawCharge odd (rawRole a) : Bit)

def rawTags (t : ℕ) (odd : Bool) : List RawTag :=
  (allRoles t).flatMap (fun a => ((rawNeighbors t a).sublists.filter (fun s => decide (s.length%2=rawCharge odd a))).map (a,·))

lemma mem_rawTags (t : ℕ) (odd : Bool) (z : RawTag) :
    z∈rawTags t odd ↔ RoleValid t z.1 ∧ z.2.Sublist (rawNeighbors t z.1) ∧ z.2.length%2=rawCharge odd z.1 := by
  rcases z with ⟨a,s⟩
  simp only [rawTags,List.mem_flatMap,List.mem_map,List.mem_filter,List.mem_sublists,decide_eq_true_eq]
  constructor
  · rintro ⟨b,hb,u,hu,he⟩
    cases he
    exact ⟨(mem_allRoles t a).mp hb,hu⟩
  · rintro ⟨ha,hs,he⟩
    exact ⟨a,(mem_allRoles t a).mpr ha,s,⟨hs,he⟩,rfl⟩

lemma cast_rawCharge (odd : Bool) (a : RawRole) : (rawCharge odd a : Bit).val=rawCharge odd a := by
  unfold rawCharge
  split <;> simp [ZMod.val_one_eq_one_mod]

lemma mod_two_charge (n : ℕ) (odd : Bool) (a : RawRole) :
    (n : Bit)=(rawCharge odd a : Bit) ↔ n%2=rawCharge odd a := by
  have hc : rawCharge odd a<2 := by unfold rawCharge; split <;> omega
  constructor
  · intro h
    have hh := congrArg ZMod.val h
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hc] using hh
  · intro h
    apply ZMod.val_injective
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hc] using h

noncomputable def rawTagEncode {t : ℕ} (odd : Bool) (z : GlobalTag t (tagCharge t odd)) : RawTag :=
  (rawRole z.1,tagOnes z.1 z.2.val)

lemma rawTagEncode_mem {t : ℕ} (odd : Bool) (z : GlobalTag t (tagCharge t odd)) :
    rawTagEncode odd z∈rawTags t odd := by
  apply (mem_rawTags t odd _).mpr
  refine ⟨rawRole_valid z.1,tagOnes_sublist z.1 z.2.val,?_⟩
  apply (mod_two_charge _ odd _).mp
  exact (tagOnes_sum z.1 z.2.val).trans z.2.property

lemma rawTags_nodup (t : ℕ) (odd : Bool) : (rawTags t odd).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro a _
    exact ((rawNeighbors_nodup t a).sublists.filter _).map (fun _ _ h => congrArg Prod.snd h)
  · apply (allRoles_nodup t).imp
    intro a b hab z ha hb
    obtain ⟨s,_,he⟩ := List.mem_map.mp ha
    obtain ⟨u,_,hf⟩ := List.mem_map.mp hb
    exact hab ((congrArg Prod.fst he).trans (congrArg Prod.fst hf).symm)

noncomputable def rawTagDecode {t : ℕ} (odd : Bool) (z : {z // z∈rawTags t odd}) :
    GlobalTag t (tagCharge t odd) := by
  classical
  have hz := (mem_rawTags t odd z.val).mp z.property
  let a := roleDecode ⟨z.val.1,hz.1⟩
  have ha : rawRole a=z.val.1 := rawRole_roleDecode ⟨z.val.1,hz.1⟩
  refine ⟨a,⟨fun v => if rawRole v.val∈z.val.2 then 1 else 0,?_⟩⟩
  rw [rawTag_sum a z.val.2 (by simpa only [ha] using hz.2.1)]
  change _=(rawCharge odd (rawRole a) : Bit)
  rw [ha]
  exact (mod_two_charge _ odd _).mpr hz.2.2

lemma tagOnes_indicator {t : ℕ} (a : TemplateVertex t) (s : List RawRole)
    (hs : s.Sublist (rawNeighbors t (rawRole a))) :
    tagOnes a (fun v => if rawRole v.val∈s then 1 else 0)=s := by
  classical
  have hmem (r : RawRole) : r∈tagOnes a (fun v => if rawRole v.val∈s then 1 else 0) ↔ r∈s := by
    by_cases hr : r∈rawNeighbors t (rawRole a)
    · have hv := (mem_rawNeighbors t _ _).mp hr
      let v := roleDecode ⟨r,hv.1⟩
      have he : rawRole v=r := rawRole_roleDecode ⟨r,hv.1⟩
      have hadj : (template t).Adj a v := (rawAdjacent_iff a v).mp (by simpa only [he] using hv.2)
      simpa only [he,ite_eq_left_iff,zero_ne_one,imp_false,not_not] using
        (mem_tagOnes a (fun v => if rawRole v.val∈s then 1 else 0) ⟨v,hadj⟩)
    · exact iff_of_false (fun h => hr ((tagOnes_sublist a _).subset h)) (fun h => hr (hs.subset h))
  apply Eq.symm
  apply List.Sublist.eq_of_length_le
  · have hf : s.filter (fun r => decide (∃ v : (template t).neighborSet a,
        rawRole v.val=r ∧ (if rawRole v.val∈s then (1 : Bit) else 0)=1))=s := by
      apply List.filter_eq_self.mpr
      intro r hr
      exact (List.mem_filter.mp ((hmem r).mpr hr)).2
    simpa only [tagOnes,hf] using hs.filter (fun r => decide (∃ v : (template t).neighborSet a,
        rawRole v.val=r ∧ (if rawRole v.val∈s then (1 : Bit) else 0)=1))
  · exact (List.Nodup.sublist (tagOnes_sublist a _) (rawNeighbors_nodup t _)).length_le_of_subset
      (fun _ h => (hmem _).mp h)

@[simp] lemma rawTagEncode_decode {t : ℕ} (odd : Bool) (z : {z // z∈rawTags t odd}) :
    rawTagEncode odd (rawTagDecode odd z)=z.val := by
  classical
  have hz := (mem_rawTags t odd z.val).mp z.property
  let a := roleDecode ⟨z.val.1,hz.1⟩
  have ha : rawRole a=z.val.1 := rawRole_roleDecode ⟨z.val.1,hz.1⟩
  change (rawRole a,tagOnes a (fun v => if rawRole v.val∈z.val.2 then 1 else 0))=z.val
  rw [tagOnes_indicator a z.val.2 (by simpa only [ha] using hz.2.1),ha]

lemma rawTagEncode_injective (t : ℕ) (odd : Bool) : Function.Injective (@rawTagEncode t odd) := by
  classical
  rintro ⟨a,z⟩ ⟨b,w⟩ he
  have hab := (rawRole_injective t) (congrArg Prod.fst he)
  change a=b at hab
  subst b
  have hzw : z=w := by
    apply Subtype.ext
    funext v
    have hone : z.val v=1 ↔ w.val v=1 := by
      rw [←mem_tagOnes a z.val v,←mem_tagOnes a w.val v]
      rw [show tagOnes a z.val=tagOnes a w.val from congrArg Prod.snd he]
    rcases bit_zero_or_one (z.val v) with hz | hz <;>
      rcases bit_zero_or_one (w.val v) with hw | hw <;> simp_all
  cases hzw
  rfl

noncomputable def rawTagEquiv (t : ℕ) (odd : Bool) :
    GlobalTag t (tagCharge t odd) ≃ {z // z∈rawTags t odd} where
  toFun z := ⟨rawTagEncode odd z,rawTagEncode_mem odd z⟩
  invFun := rawTagDecode odd
  left_inv _z := rawTagEncode_injective t odd (rawTagEncode_decode odd _)
  right_inv z := Subtype.ext (rawTagEncode_decode odd z)

end ParityWL.Complexity

end OAI
