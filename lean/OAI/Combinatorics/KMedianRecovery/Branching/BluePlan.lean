import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.BestDesignation
import OAI.Combinatorics.KMedianRecovery.Branching.BlueNextTable

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {L R Y : Type*} [LinearOrder L] [LinearOrder R] [LinearOrder Y]
omit [LinearOrder R] in
lemma spec_mono (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (U : Finset L)
    (c d : ℕ) (hcd : c≤d) (x : Candidate (List (Atom L R Y))) (hx : Spec B F label q U c x) : Spec B F label q U d x := by
  cases x with
  | none=>trivial
  | some x=>exact ⟨hx.1,hx.2.1,hx.2.2.1.trans hcd,hx.2.2.2⟩
lemma recurrence_spec (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (t : ℕ) (U : Finset L) :
    Spec B F label q U t (recurrence (block B F label q) t U) := by
  induction t generalizing U with
  | zero=>
    rw [recurrence]
    split_ifs with h
    · subst U;exact empty_spec B F label q 0
    · trivial
  | succ t ih=>
    rw [recurrence]
    apply select_spec _ _ trivial
    intro x hx
    obtain ⟨V,hV,rfl⟩:=List.mem_map.mp hx
    have hVU := (BlueSubsetDP.mem_blocks.mp (enumBlocks_set U ▸ List.mem_toFinset.mpr hV)).2
    have hd : Disjoint V (U\V) := by
      apply Finset.disjoint_left.mpr
      intro l hl hrest
      exact (Finset.mem_sdiff.mp hrest).2 hl
    have hu : V∪(U\V)=U := by
      ext l
      simp only [Finset.mem_union,Finset.mem_sdiff]
      exact ⟨fun h=>h.elim (hVU ·) And.left,fun h=>by by_cases hV : l∈V;exact Or.inl hV;exact Or.inr ⟨h,hV⟩⟩
    have hh:=merge_spec B F label q V (U\V) 1 t _ _ (block_spec B F label q V) (ih (U\V)) hd
    simpa only [hu,Nat.add_comm 1] using hh
lemma best_spec (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (c : ℕ) (U : Finset L) :
    Spec B F label q U c (best (block B F label q) c U) := by
  unfold best
  split_ifs with h
  · subst U;exact empty_spec B F label q c
  · apply select_spec _ _ trivial
    intro x hx
    obtain ⟨t,ht,rfl⟩:=List.mem_map.mp hx
    exact spec_mono B F label q U (t+1) c (by have hh:=List.mem_range.mp ht;omega) _
      (recurrence_spec B F label q (t+1) U)
def pick (r0 : R) (y0 : Y) (xs : List (Atom L R Y)) (l : L) : Atom L R Y :=
  (xs.find? (fun a=>a.1=l)).getD (l,r0,y0)
omit [LinearOrder R] [LinearOrder Y] in
lemma pick_mem (r0 : R) (y0 : Y) (xs : List (Atom L R Y)) (l : L) (hl : l∈(labels xs).toFinset) :
    pick r0 y0 xs l∈xs ∧ (pick r0 y0 xs l).1=l := by
  obtain ⟨a,ha,hal⟩:=List.mem_map.mp (List.mem_toFinset.mp hl)
  have hn : xs.find? (fun a=>a.1=l)≠none := by
    intro he
    exact List.find?_eq_none.mp he a ha (decide_eq_true hal)
  obtain ⟨b,hb⟩:=Option.ne_none_iff_exists'.mp hn
  simp only [pick,hb,Option.getD_some]
  exact ⟨List.mem_of_find?_eq_some hb,of_decide_eq_true (List.find?_some (p := fun a : Atom L R Y => decide (a.1=l)) hb)⟩
omit [LinearOrder R] [LinearOrder Y] in
lemma pick_eq (r0 : R) (y0 : Y) (xs : List (Atom L R Y)) (hn : (labels xs).Nodup)
    (a : Atom L R Y) (ha : a∈xs) : pick r0 y0 xs a.1=a := by
  have hp:=pick_mem r0 y0 xs a.1 (List.mem_toFinset.mpr (List.mem_map.mpr ⟨a,ha,rfl⟩))
  exact List.inj_on_of_nodup_map hn hp.1 ha hp.2
omit [LinearOrder R] [LinearOrder Y] in
lemma cost_pick (r0 : R) (y0 : Y) (q : R→Y→ℚ) (xs : List (Atom L R Y)) (U : Finset L) (h : Route U xs) :
    (∑ l∈U,q (pick r0 y0 xs l).2.1 (pick r0 y0 xs l).2.2)=cost q xs := by
  rw [←h.2,List.sum_toFinset _ h.1]
  simp only [labels,List.map_map,Function.comp_def,cost]
  congr 1
  apply List.map_congr_left
  intro a ha
  rw [pick_eq r0 y0 xs h.1 a ha]
variable [Fintype L]
noncomputable def makePlan (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (c : ℕ)
    (r0 : R) (y0 : Y) (k : ℚ) (xs : List (Atom L R Y))
    (h : best (block B F label q) c Finset.univ=some (k,xs)) : BlueSubsetDP.Plan B F label (fun r y=>(q r y:ℝ)) c := by
  have hs:=best_spec B F label q c Finset.univ
  rw [h] at hs
  let sel : L→R := fun l=>(pick r0 y0 xs l).2.1
  let dst : L→Y := fun l=>(pick r0 y0 xs l).2.2
  have hp (l : L) := pick_mem r0 y0 xs l (hs.1.2 ▸ Finset.mem_univ l)
  have hv (l : L) : sel l∈B ∧ label (sel l)=l ∧ dst l∈F := by
    have hh:=hs.2.1 _ (hp l).1
    exact ⟨hh.1,hh.2.1.trans (hp l).2,hh.2.2⟩
  refine ⟨sel,dst,hv,?_,?_,?_⟩
  · intro l m he
    exact (hv l).2.1.symm.trans ((congrArg label he).trans (hv m).2.1)
  · apply (Finset.card_le_card ?_).trans hs.2.2.1
    intro y hy
    obtain ⟨l,_,rfl⟩:=Finset.mem_image.mp hy
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨_,(hp l).1,rfl⟩)
  · have hk : (∑ l,q (sel l) (dst l))=k := by
      simpa only [sel,dst] using (cost_pick r0 y0 q xs Finset.univ hs.1).trans hs.2.2.2.symm
    have hh:=optimizer_value B F label q c Finset.univ
    rw [h] at hh
    rw [←hh]
    change (((∑ l,(q (sel l) (dst l):ℝ)):ℝ):WithTop ℝ)=((k:ℝ):WithTop ℝ)
    rw [←Rat.cast_sum,hk]
end MetricKMedianRecovery.BlueDP

namespace MetricKMedianRecovery.BlueDP
variable {L R Y : Type*} [LinearOrder L] [LinearOrder R] [LinearOrder Y]
omit [LinearOrder R] [LinearOrder Y] in
lemma route_length (U : Finset L) (xs : List (Atom L R Y)) (h : Route U xs) : xs.length=U.card := by
  rw [←h.2,List.toFinset_card_of_nodup h.1]
  exact (List.length_map ..).symm
end MetricKMedianRecovery.BlueDP
namespace MetricKMedianRecovery.BitMachine.BinaryBlueSize
open WordOperations WordList RationalHeight
variable {L R : Type*} [LinearOrder L] [LinearOrder R] {n : ℕ}
omit [LinearOrder L] in
lemma atom_bound (el : L→List Bool) (er : R→List Bool) (B : Finset R) (F : Finset (Fin n))
    (label : R→L) (q : R→Fin n→ℚ) (a : BlueDP.Atom L R (Fin n)) (h : a.2.1∈B ∧ label a.2.1=a.1 ∧ a.2.2∈F) :
    let N:=(BinaryBlueItem.records el er B label q).length
    (BinaryBlueItem.atomEnc el er a).length≤5*N+2 ∧ Height (q a.2.1 a.2.2) N := by
  dsimp only
  have hr : (BinaryBlueItem.record el er label q a.2.1).length≤(BinaryBlueItem.records el er B label q).length :=
    length_member_le_encode (List.mem_map.mpr ⟨a.2.1,(Finset.mem_sort (·≤·)).mpr h.1,rfl⟩)
  have hq := RationalArray.input_height (List.ofFn (q a.2.1)) (q a.2.1 a.2.2) (List.mem_ofFn.mpr ⟨a.2.2,rfl⟩)
  have hn : n≤(RationalArray.encode (List.ofFn (q a.2.1))).length := by
    simpa only [RationalArray.encode,List.length_map,List.length_ofFn] using
      length_le_encode ((List.ofFn (q a.2.1)).map BinaryRational.encode)
  have hb : a.2.2.val.bits.length≤n := (by rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr Nat.lt_two_pow_self : a.2.2.val.bits.length≤a.2.2.val).trans (Nat.le_of_lt a.2.2.isLt)
  simp only [BinaryBlueItem.record,pairBits_length] at hr
  refine ⟨?_,hq.mono (by omega)⟩
  simp only [BinaryBlueItem.atomEnc,pairBits_length]
  rw [←h.2.1]
  omega
lemma candidate_bound (el : L→List Bool) (er : R→List Bool) (B : Finset R) (F : Finset (Fin n))
    (label : R→L) (q : R→Fin n→ℚ) (U : Finset L) (c : ℕ) (x : BlueDP.Candidate (List (BlueDP.Atom L R (Fin n))))
    (hx : BlueDP.Spec B F label q U c x) :
    let N:=(BinaryBlueItem.records el er B label q).length
    (BinaryBlueChoice.encode (BinaryBlueMerge.listEnc (BinaryBlueItem.atomEnc el er)) x).length≤
      40*(U.card+1)*(N+1) := by
  dsimp only
  cases x with
  | none=>simp [BinaryBlueChoice.encode]
  | some x=>
    rcases x with ⟨k,xs⟩
    obtain ⟨hr,hv,_,hk⟩:=hx
    have hl:=BlueDP.route_length U xs hr
    have ha (a) (hax : a∈xs):=(atom_bound el er B F label q a (hv a hax)).1
    have hheight : Height k (xs.length*((BinaryBlueItem.records el er B label q).length+1)) := by
      rw [hk]
      simpa only [BlueDP.cost,List.length_map] using RationalHeight.list_sum
        (xs.map (fun a=>q a.2.1 a.2.2)) (BinaryBlueItem.records el er B label q).length (by
          intro z hz
          obtain ⟨a,hax,rfl⟩:=List.mem_map.mp hz
          exact (atom_bound el er B F label q a (hv a hax)).2)
    have hscore := BinaryRational.encode_height hheight
    have hlist := Subsets.encode_bound (xs.map (BinaryBlueItem.atomEnc el er))
      (5*(BinaryBlueItem.records el er B label q).length+2) (by
        intro z hz
        obtain ⟨a,hax,rfl⟩:=List.mem_map.mp hz
        exact ha a hax)
    simp only [List.length_map] at hlist
    simp only [BinaryBlueChoice.encode,WordList.encode,length_cons,List.length_nil,pairBits_length,BinaryBlueMerge.listEnc]
    rw [←hl]
    nlinarith
end MetricKMedianRecovery.BitMachine.BinaryBlueSize

end OAI
