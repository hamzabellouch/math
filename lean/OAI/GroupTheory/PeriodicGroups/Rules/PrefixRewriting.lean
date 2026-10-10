import Mathlib
import OAI.GroupTheory.PeriodicGroups.Rules.BoundaryCell

namespace OAI

universe u v w
namespace SourceBurnside.FiniteTable
section
open LocalSyntax LocalSyntax.Skeleton
variable {q d N : ℕ} [NeZero q]
namespace Cell
lemma left_format (c : Cell q) (S : Schedule q) (hc : c.PayloadFormat d)
    (hl : ¬c.skeleton.last) : (c.wing .left).Format S d := by
  dsimp [PayloadFormat,Cell.isPalette,Cell.isCore,Cell.pos] at hc
  simp only [Format,wing,marker,metadata,pos,isPalette,isCore,Skeleton.Admissible,
    Skeleton.IsHead,Skeleton.mark]
  simpa only [reduceCtorEq,false_implies,true_implies,or_self,and_true,true_and,
    implies_true,defaultHead,Skeleton.last] using And.intro hl (And.intro hc.1 (And.intro hc.2.1 hc.2.2))
end Cell

structure AcquiredPrefix (q d : ℕ) where
  size : ℕ
  positive : 0<size
  cell : Fin size → Cell q
  first_iff : ∀ i, (cell i).skeleton.first ↔ i.val=0
  adjacent : ∀ i j, i.val+1=j.val →
    Skeleton.Structural (cell i).skeleton (cell j).skeleton ∧
      Skeleton.Internal (cell i).skeleton (cell j).skeleton
  payload_format : ∀ i, (cell i).PayloadFormat d

namespace AcquiredPrefix
variable (R : AcquiredPrefix q d) (S : Schedule q)
def first : Fin R.size := ⟨0,R.positive⟩
def last : Fin R.size := ⟨R.size-1,by have := R.positive; omega⟩
omit [NeZero q] in
lemma first_first : (R.cell R.first).skeleton.first := (R.first_iff _).mpr rfl

def boundaryCell (cursor : Fin R.size) (s : Bool) (i : Fin R.size) : Cell q :=
  if i<cursor then (R.cell i).wing .left else
    if i=cursor then (R.cell i).boundary s else (R.cell i).idle s

def boundaryWord (cursor : Fin R.size) (s : Bool) : List (Cell q) :=
  List.ofFn (R.boundaryCell cursor s)
def idleWord (s : Bool) : List (Cell q) := List.ofFn (fun i => (R.cell i).idle s)

lemma boundaryCell_format (cursor : Fin R.size) (s : Bool)
    (hs : ∀ i, (R.cell i).metadata.zeroTask=true → s=false) (i : Fin R.size) :
    (R.boundaryCell cursor s i).Format S d := by
  unfold boundaryCell
  split
  · rename_i hi
    apply Cell.left_format _ S (R.payload_format i)
    let j : Fin R.size := ⟨i.val+1,by have := cursor.isLt; change i.val<cursor.val at hi; omega⟩
    exact (R.adjacent i j rfl).2.2.2.2.2
  · split
    · exact Cell.boundary_format _ S s (R.payload_format i) (hs i)
    · exact Cell.idle_format _ S s (R.payload_format i)

lemma boundaryCell_cursor (cursor : Fin R.size) (s : Bool) :
    R.boundaryCell cursor s cursor=(R.cell cursor).boundary s := by simp [boundaryCell]

omit [NeZero q] in
lemma acquisition_pair (i j : Fin R.size) (hij : i.val+1=j.val) :
    Skeleton.Pair ((R.cell i).skeleton.mark .left) ((R.cell j).skeleton.mark .boundary) := by
  obtain ⟨hstr,hi⟩ := R.adjacent i j hij
  refine ⟨hstr,Or.inr ?_⟩
  simp only [Skeleton.rightExternal,Skeleton.leftExternal,Skeleton.mark_marker,
    Skeleton.mark_last,Skeleton.mark_first,Skeleton.acceptsRight,Skeleton.acceptsLeft,
    Skeleton.internal_mark_left,Skeleton.internal_mark_right]
  simpa using And.intro hi.2.2.2.1 hi

lemma release_step (i j : Fin R.size) (hij : i.val+1=j.val) (s : Bool)
    (hs : ∀ i, (R.cell i).metadata.zeroTask=true → s=false) :
    Step S d (R.boundaryWord j s) (R.boundaryWord i s) := by
  unfold boundaryWord
  apply step_two_ofFn _ _ i j hij
  · intro z hzi hzj
    have hi : z < i ↔ z < j := by
      have hzine : z.val≠i.val := fun h => hzi (Fin.ext h)
      have hzjne : z.val≠j.val := fun h => hzj (Fin.ext h)
      simp only [Fin.lt_def]
      omega
    simp only [boundaryCell,hi,hzi,hzj,ite_false]
  · have hij' : i < j := by simp only [Fin.lt_def]; omega
    have hji : ¬ j < i := by omega
    have hne : j≠i := by omega
    refine ⟨?_,Or.inr ⟨_,_,_,_,rfl,rfl,Or.inr ?_⟩⟩
    · intro c hc
      simp only [List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl <;> apply R.boundaryCell_format S _ s hs
    · simpa only [boundaryCell,hij',hji,hne,ne_eq,hne,ite_true,ite_false,lt_self_iff_false]
        using Binary.acquire (S:=S) (R.cell i) (R.cell j) s (R.acquisition_pair i j hij)

lemma remove_first (s : Bool) (hs : ∀ i, (R.cell i).metadata.zeroTask=true → s=false) :
    Step S d (R.boundaryWord R.first s) (R.idleWord s) := by
  unfold boundaryWord idleWord
  apply step_one_ofFn _ _ R.first
  · intro i hi
    have hlt : ¬ i < R.first := by change ¬ i.val < 0; omega
    simp [boundaryCell,hlt,hi]
  · refine ⟨?_,Or.inl ⟨_,_,rfl,rfl,Or.inr ?_⟩⟩
    · intro c hc
      simp only [List.singleton_append,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl
      · exact R.boundaryCell_format S _ s hs _
      · exact Cell.idle_format _ S s (R.payload_format _)
    · rw [R.boundaryCell_cursor]
      exact Unary.create _ _ R.first_first

theorem release (cursor : Fin R.size) (s : Bool) (hs : ∀ i, (R.cell i).metadata.zeroTask=true → s=false) :
    Reach S d (R.boundaryWord cursor s) (R.idleWord s) := by
  generalize he : cursor.val=n
  induction n generalizing cursor with
  | zero =>
    have hx : cursor=R.first := Fin.ext he
    subst cursor
    exact Relation.ReflTransGen.single (R.remove_first S s hs)
  | succ n ih =>
    let i : Fin R.size := ⟨n,by omega⟩
    have he' : i.val+1=cursor.val := by dsimp [i]; omega
    exact (Relation.ReflTransGen.single (R.release_step S i cursor he' s hs)).trans
      (ih i rfl)

end AcquiredPrefix

namespace Cell
lemma wing_self {S : Schedule q} (c : Cell q) (m : Marker) (hf : c.Format S d)
    (hm : c.marker=m) (hw : m=.left ∨ m=.right) : c.wing m=c := by
  have hd := hf.2.2.2.2.2.1 (by rwa [hm])
  cases c with
  | mk sk ch da ce hd' =>
    cases sk
    simp_all [wing,Skeleton.mark,marker]

lemma boundary_self {S : Schedule q} (c : Cell q) (hf : c.Format S d)
    (hm : c.marker=.boundary) : c.boundary c.head.side=c := by
  have hd := hf.2.2.2.2.2.2.1 hm
  cases c with
  | mk sk ch da ce hd' =>
    cases sk
    cases hd'
    simp_all [boundary,defaultHead,Skeleton.mark,marker]

@[simp] lemma idle_marker (c : Cell q) (s : Bool) : (c.idle s).marker=.idle := rfl
end Cell

namespace Component
variable (f : Fin N → Cell q) (i : Fin N)
omit [NeZero q] in
lemma boundary_right (hi : (f i).marker=.boundary) : right f i=i := by
  apply le_antisymm
  · by_contra hh
    have hn : i.val<(right f i).val := by omega
    exact (connected_right f i).right_barrier hn (Or.inr (Or.inl hi))
  · exact self_le_right f i

noncomputable def partialRegion {S : Schedule q} (hs : Syntax S d (List.ofFn f))
    (hi : (f i).marker=.boundary) : AcquiredPrefix q d where
  size := size f i
  positive := size_pos f i
  cell := fun j => f (offset f i j)
  first_iff := offset_first_iff f i (Verification.coherent_of_syntax S hs)
    (exterior_of_syntax hs) (Or.inl hi)
  adjacent j k hj := ⟨(Verification.coherent_of_syntax S hs _ _ (offset_adjacent f i j k hj)).1,
    offset_internal f i (Verification.coherent_of_syntax S hs) j k hj⟩
  payload_format j := by
    have hh : (f (offset f i j)).Format S d := hs.2.2 _ (List.mem_ofFn.mpr ⟨offset f i j,rfl⟩)
    exact ⟨hh.2.1,hh.2.2.1,hh.2.2.2.1⟩

lemma headIndex_prefix_last {S : Schedule q} (hs : Syntax S d (List.ofFn f))
    (hi : (f i).marker=.boundary) : headIndex f i=(partialRegion f i hs hi).last := by
  have h := boundary_right f i hi
  have hl := left_le_self f i
  apply Fin.ext
  change i.val-(left f i).val=size f i-1
  dsimp [size]
  rw [h]
  omega

theorem actual_partial_release {S : Schedule q} (hs : Syntax S d (List.ofFn f))
    (hi : (f i).marker=.boundary) :
    Reach S d (List.ofFn (partialRegion f i hs hi).cell)
      ((partialRegion f i hs hi).idleWord (f i).head.side) := by
  let P := partialRegion f i hs hi
  have hf (j : Fin P.size) : (P.cell j).Format S d :=
    hs.2.2 _ (List.mem_ofFn.mpr ⟨offset f i j,rfl⟩)
  have hh : P.cell (headIndex f i)=f i := by
    change f (offset f i (headIndex f i))=f i
    rw [offset_headIndex]
  have he : P.boundaryWord (headIndex f i) (f i).head.side=List.ofFn P.cell := by
    dsimp only [P,partialRegion,AcquiredPrefix.boundaryWord,AcquiredPrefix.boundaryCell]
    apply congrArg List.ofFn
    funext j
    unfold AcquiredPrefix.boundaryCell
    dsimp only
    split
    · apply Cell.wing_self _ _ (hf j)
        (before_head f i (Verification.coherent_of_syntax S hs) (Or.inl hi) j ‹_›) (Or.inl rfl)
    · rename_i hj
      have hle : j≤headIndex f i := by
        rw [headIndex_prefix_last f i hs hi]
        change j.val ≤ size f i - 1
        have hjlt : j.val<size f i := j.isLt
        omega
      have hje : j=headIndex f i := le_antisymm hle (le_of_not_gt hj)
      subst j
      rw [ite_eq_left rfl,offset_headIndex]
      exact Cell.boundary_self _ (hs.2.2 _ (List.mem_ofFn.mpr ⟨i,rfl⟩)) hi
  rw [←he]
  apply P.release S
  intro j hj
  have ht := SameRegion.task (Verification.coherent_of_syntax S hs) (connected_offset f i j).symm
  have hz : (P.cell j).metadata.zeroTask=(f i).metadata.zeroTask := congrArg Task.zeroTask ht
  apply (hs.2.2 _ (List.mem_ofFn.mpr ⟨i,rfl⟩)).2.2.2.2.2.2.2.1 (Or.inl hi)
  exact hz.symm.trans hj
end Component
end

section
open LocalSyntax LocalSyntax.Skeleton
variable {q d N : ℕ} [NeZero q] {S : Schedule q}

def lockedCount (w : List (Cell q)) : ℕ := w.countP (fun c => decide (c.marker≠.idle))
omit [NeZero q] in
lemma lockedCount_eq_zero (w : List (Cell q)) : lockedCount w=0 ↔ ∀ c∈w,c.marker=.idle := by
  simp [lockedCount,List.countP_eq_zero]
omit [NeZero q] in
lemma lockedCount_pos (w : List (Cell q)) : 0<lockedCount w ↔ ∃ c∈w,c.marker≠.idle := by
  simp [lockedCount,List.countP_pos_iff]
omit [NeZero q] in
@[simp] lemma lockedCount_append (v w : List (Cell q)) :
    lockedCount (v++w)=lockedCount v+lockedCount w := List.countP_append

namespace Component
variable (f : Fin N → Cell q) (i : Fin N)
noncomputable def word : List (Cell q) := List.ofFn (fun j => f (offset f i j))

omit [NeZero q] in
lemma word_slice : word f i=((List.ofFn f).drop (left f i).val).take (size f i) := by
  have hs : size f i≤N-(left f i).val := by
    have := (right f i).isLt
    dsimp [size]
    omega
  apply List.ext_getElem
  · simp only [word,List.length_ofFn,List.length_take,List.length_drop,min_eq_left hs]
  · intro n hn hn'
    simp only [word,List.getElem_ofFn,List.getElem_take,List.getElem_drop]
    apply congrArg f
    apply Fin.ext
    rfl

omit [NeZero q] in
lemma word_split : List.ofFn f=
    (List.ofFn f).take (left f i).val++word f i++(List.ofFn f).drop ((right f i).val+1) := by
  have he : (left f i).val+size f i=(right f i).val+1 := by
    have := left_le_right f i
    dsimp [size]
    omega
  rw [word_slice]
  rw [show (right f i).val+1=(left f i).val+size f i from he.symm]
  rw [←List.drop_drop,List.append_assoc,List.take_append_drop,List.take_append_drop]

omit [NeZero q] in
lemma word_infix : word f i <:+: List.ofFn f := by
  exact ⟨_,_,(word_split f i).symm⟩

omit [NeZero q] in
lemma word_head_mem : f i∈word f i := by
  exact List.mem_ofFn.mpr ⟨headIndex f i,congrArg f (offset_headIndex f i)⟩

omit [NeZero q] in
lemma word_locked_pos (hi : (f i).skeleton.IsHead) : 0<lockedCount (word f i) := by
  apply (lockedCount_pos _).mpr
  refine ⟨f i,word_head_mem f i,?_⟩
  rcases hi with hi|hi <;> change (f i).marker=_ at hi <;> rw [hi] <;> decide

theorem normalize (hs : Syntax S d (List.ofFn f)) (hw : Survives S d (List.ofFn f))
    (hi : (f i).skeleton.IsHead) :
    ∃ v, Reach S d (word f i) v ∧ lockedCount v=0 := by
  rcases hi with hi|hi
  · let P := partialRegion f i hs hi
    refine ⟨P.idleWord (f i).head.side,actual_partial_release f i hs hi,?_⟩
    apply (lockedCount_eq_zero _).mpr
    intro c hc
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hc
    rfl
  · let R := region f i hs hi
    have hh := actual_rollback_release f i hs hi
    rcases hh with hh | ⟨w,p,a,s,hh,he,hz⟩
    · refine ⟨R.idleWord (f i).head.side,hh,?_⟩
      apply (lockedCount_eq_zero _).mpr
      intro c hc
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hc
      rfl
    · have hsurv := hw.infix (word_infix f i)
      exact (hsurv p [a] s (by simpa only [he,word,region] using hh) hz).elim
end Component

theorem Survives.transactions_idle {w : List (Cell q)} (hw : Survives S d w)
    (hs : Syntax S d w) : ∃ v, Reach S d w v ∧ ∀c∈v,c.marker=.idle := by
  generalize hk : lockedCount w=n
  induction n using Nat.strong_induction_on generalizing w with
  | h n ih =>
    by_cases hn : lockedCount w=0
    · exact ⟨w,.refl,(lockedCount_eq_zero w).mp hn⟩
    · obtain ⟨c,hc,hnc⟩ := (lockedCount_pos w).mp (Nat.pos_of_ne_zero hn)
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp hc
      let f : Fin w.length → Cell q := w.get
      have hf : List.ofFn f=w := List.ofFn_get w
      have hsf : Syntax S d (List.ofFn f) := by rwa [hf]
      have hwf : Survives S d (List.ofFn f) := by rwa [hf]
      have hi' : (f i).marker≠.idle := by change (w.get i).marker≠.idle; rwa [hi]
      obtain ⟨h,_,hhead⟩ := (Verification.coherent_of_syntax S hsf).owner
        (exterior_of_syntax hsf) i hi'
      obtain ⟨v,hv,hvc⟩ := Component.normalize f h hsf hwf hhead
      let p := (List.ofFn f).take (Component.left f h).val
      let s := (List.ofFn f).drop ((Component.right f h).val+1)
      have he : w=p++Component.word f h++s := hf.symm.trans (Component.word_split f h)
      have hr : Reach S d w (p++v++s) := by rw [he]; exact reach_context hv p s
      have hpos := Component.word_locked_pos f h hhead
      have hless : lockedCount (p++v++s)<n := by
        rw [←hk,he]
        simp only [lockedCount_append,hvc]
        omega
      obtain ⟨z,hz,hzi⟩ := ih (lockedCount (p++v++s)) hless
        (hw.of_reach hr) (reach_syntax hr hs) rfl
      exact ⟨z,hr.trans hz,hzi⟩
end

open LocalSyntax LocalSyntax.Skeleton
variable {q d : ℕ} [NeZero q] {S : Schedule q}

abbrev StructuralChain (w : List (Cell q)) :=
  w.IsChain (fun a b => Skeleton.Structural a.skeleton b.skeleton)

def EndsStop (w : List (Cell q)) : Prop := ∀c∈w.getLast?,c.pos=.stop

omit [NeZero q] in
lemma endsStop_cons_tail {c b : Cell q} {w : List (Cell q)}
    (h : EndsStop (c::b::w)) : EndsStop (b::w) := by
  simpa [EndsStop] using h

omit [NeZero q] in
lemma coreRange_cons (p : Fin q) : (List.finRange q).drop p.val=
    p::(List.finRange q).drop (p.val+1) := by
  rw [List.drop_eq_getElem_cons (by simp)]
  simp

omit [NeZero q] in
lemma scan_core (w : List (Cell q)) (c : Cell q) (p : Fin q)
    (hc : c.pos=.core p) (hchain : StructuralChain (c::w)) (hlast : EndsStop (c::w)) :
    ∃ cores b s, c::w=cores++b::s ∧
      cores.map Cell.pos=((List.finRange q).drop p.val).map Position.core ∧ b.isPalette := by
  induction w generalizing c p with
  | nil =>
    have hz := hlast c (by simp)
    rw [hc] at hz
    cases hz
  | cons b w ih =>
    obtain ⟨hcb,hbw⟩ := List.isChain_cons_cons.mp hchain
    have hlast' := endsStop_cons_tail hlast
    change c.skeleton.pos=.core p at hc
    cases hp : b.pos with
    | core r =>
      change b.skeleton.pos=.core r at hp
      have hn : p.val+1=r.val := by simpa only [Skeleton.Structural,hc,hp] using hcb
      obtain ⟨cores,z,s,he,hcores,hz⟩ := ih b r hp hbw hlast'
      refine ⟨c::cores,z,s,by simp only [List.cons_append,he],?_,hz⟩
      rw [coreRange_cons p,List.map_cons,List.map_cons]
      rw [show c.pos=.core p from hc,hcores,hn]
    | palette x =>
      change b.skeleton.pos=.palette x at hp
      have hn : p.val+1=q := by simpa only [Skeleton.Structural,hc,hp] using hcb
      refine ⟨[c],b,w,rfl,?_,⟨x,hp⟩⟩
      have hdrop : (List.finRange q).drop q=[] := List.drop_eq_nil_iff.mpr (by simp)
      rw [coreRange_cons p,hn,hdrop]
      simp only [List.map_cons,List.map_nil]
      exact congrArg (fun z => [z]) hc
    | stop =>
      change b.skeleton.pos=.stop at hp
      simp only [Skeleton.Structural,hc,hp] at hcb

omit [NeZero q] in
lemma scan_palette (w : List (Cell q)) (c : Cell q) (hc : c.isPalette)
    (hchain : StructuralChain (c::w)) (hlast : EndsStop (c::w)) :
    ∃ pal z s, c::w=pal++z::s ∧ pal≠[] ∧ (∀a∈pal,a.isPalette) ∧ z.pos=.stop := by
  induction w generalizing c with
  | nil =>
    obtain ⟨x,hx⟩ := hc
    have hz := hlast c (by simp)
    rw [hx] at hz
    cases hz
  | cons b w ih =>
    obtain ⟨hcb,hbw⟩ := List.isChain_cons_cons.mp hchain
    obtain ⟨x,hx⟩ := hc
    change c.skeleton.pos=.palette x at hx
    cases hp : b.pos with
    | palette y =>
      obtain ⟨pal,z,s,he,hpn,hpall,hz⟩ := ih b ⟨y,hp⟩ hbw (endsStop_cons_tail hlast)
      refine ⟨c::pal,z,s,by simp only [List.cons_append,he],List.cons_ne_nil _ _,?_,hz⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl|ha
      · exact ⟨x,hx⟩
      · exact hpall a ha
    | core p =>
      change b.skeleton.pos=.core p at hp
      simp only [Skeleton.Structural,hx,hp] at hcb
    | stop =>
      refine ⟨[c],b,w,rfl,by simp,?_,hp⟩
      intro a ha
      have he := List.mem_singleton.mp ha
      subst a
      exact ⟨x,hx⟩

structure StructuralBlock (q : ℕ) where
  cores : List (Cell q)
  core_positions : cores.map Cell.pos=(List.finRange q).map Position.core
  palette : List (Cell q)
  palette_nonempty : palette≠[]
  palette_positions : ∀c∈palette,c.isPalette
  stop : Cell q
  stop_position : stop.pos=.stop
namespace StructuralBlock
variable (B : StructuralBlock q)
def word : List (Cell q) := B.cores++B.palette++[B.stop]
omit [NeZero q] in
lemma cores_length : B.cores.length=q := by
  have h := congrArg List.length B.core_positions
  simpa using h
omit [NeZero q] in
lemma word_nonempty : B.word≠[] := by
  simp [word]
end StructuralBlock

omit [NeZero q] in
lemma endsStop_suffix (p w : List (Cell q)) (h : EndsStop (p++w)) : EndsStop w := by
  intro a ha
  apply h a
  change (p++w).getLast?=some a
  change w.getLast?=some a at ha
  rw [List.getLast?_append,ha]
  rfl

lemma scan_block (w : List (Cell q)) (c : Cell q) (hc : c.pos=.core (0 : Fin q))
    (hchain : StructuralChain (c::w)) (hlast : EndsStop (c::w)) :
    ∃ B : StructuralBlock q, ∃ s, c::w=B.word++s := by
  obtain ⟨cores,b,s,he,hcpos,hb⟩ := scan_core w c 0 hc hchain hlast
  have hchain' : StructuralChain (b::s) := (List.isChain_append.mp (he ▸ hchain)).2.1
  have hlast' : EndsStop (b::s) := endsStop_suffix cores _ (he ▸ hlast)
  obtain ⟨pal,z,t,hpal,hpn,hpp,hzp⟩ := scan_palette s b hb hchain' hlast'
  let B : StructuralBlock q := ⟨cores,by simpa using hcpos,pal,hpn,hpp,z,hzp⟩
  exact ⟨B,t,by simpa [B,StructuralBlock.word,hpal,List.append_assoc] using he⟩

def StartsCore (w : List (Cell q)) : Prop := ∀c∈w.head?,c.pos=.core (0 : Fin q)

namespace StructuralBlock
variable (B : StructuralBlock q)
omit [NeZero q] in
lemma last_stop : B.word.getLast?=some B.stop := by simp [word]

lemma starts_after {w : List (Cell q)} (hc : StructuralChain (B.word++w)) : StartsCore w := by
  intro a ha
  have h := (List.isChain_append.mp hc).2.2 B.stop (by rw [B.last_stop]; rfl) a ha
  have hz : B.stop.skeleton.pos=.stop := B.stop_position
  cases hp : a.pos with
  | core p =>
    change a.skeleton.pos=.core p at hp
    have h0 : p.val=0 := by simpa only [Skeleton.Structural,hz,hp] using h
    have hp0 : p=(0 : Fin q) := Fin.ext (by simpa using h0)
    exact congrArg Position.core hp0
  | palette x =>
    change a.skeleton.pos=.palette x at hp
    simp only [Skeleton.Structural,hz,hp] at h
  | stop =>
    change a.skeleton.pos=.stop at hp
    simp only [Skeleton.Structural,hz,hp] at h
end StructuralBlock

theorem structural_decompose (w : List (Cell q)) (hc : StructuralChain w)
    (hs : StartsCore w) (hl : EndsStop w) :
    ∃ bs : List (StructuralBlock q), w=bs.flatMap StructuralBlock.word := by
  generalize hn : w.length=n
  induction n using Nat.strong_induction_on generalizing w with
  | h n ih =>
    cases w with
    | nil => exact ⟨[],rfl⟩
    | cons c w =>
      obtain ⟨B,s,he⟩ := scan_block w c (hs c (by simp)) hc hl
      have hsc : StructuralChain (B.word++s) := he ▸ hc
      have hlen : s.length<n := by
        have hh := congrArg List.length he
        have hp := List.length_pos_iff.mpr B.word_nonempty
        simp only [List.length_append] at hh
        omega
      obtain ⟨bs,hbs⟩ := ih s.length hlen s (List.isChain_append.mp hsc).2.1
        (B.starts_after hsc) (endsStop_suffix B.word s (he ▸ hl)) rfl
      exact ⟨B::bs,by simpa only [List.flatMap_cons,←hbs] using he⟩

namespace Cell
lemma stop_idle_canonical (c : Cell q) (bits : Fin d → ZMod 2)
    (hf : c.Format S d) (hp : c.pos=.stop) (hm : c.marker=.idle) :
    c=canonicalCell bits .stop := by
  have hch := hf.2.1 (by simp [isPalette,hp])
  have hc' := hf.2.2.2.1 (by simp [isCore,hp])
  have hm' := hf.2.2.2.2.1 hm
  have hmeta := hm'.1
  have hhead := hm'.2.1
  have hd := hc'.1
  have hz := hc'.2
  have hsk : c.skeleton=⟨.stop,.idle,defaultMeta⟩ := by
    cases c with
    | mk sk ch dat cert head => cases sk; simp_all [marker,pos,metadata]
  cases c with
  | mk sk ch dat cert head =>
    simp_all [canonicalCell]
    rfl

lemma core_idle_canonical (c : Cell q) (bits : Fin d → ZMod 2) (p : Fin q)
    (hf : c.Format S d) (hp : c.pos=.core p) (hm : c.marker=.idle)
    (hb : ∀ h:p.val<d,c.data false=bits ⟨p.val,h⟩) :
    c=canonicalCell bits (.core p) := by
  have hch := hf.2.1 (by simp [isPalette,hp])
  have hm' := hf.2.2.2.2.1 hm
  have hmeta := hm'.1
  have hhead := hm'.2.1
  have hz := hm'.2.2.2
  have hd : c.data=(canonicalCell bits (.core p)).data := by
    funext side
    cases side with
    | true => exact hm'.2.2.1
    | false =>
      dsimp only [canonicalCell]
      by_cases h : p.val<d
      · simpa [h] using hb h
      · have hd := hf.2.2.1 p hp (Nat.le_of_not_gt h)
        simpa [h] using congrFun hd false
  have hsk : c.skeleton=⟨.core p,.idle,defaultMeta⟩ := by
    cases c with
    | mk sk ch dat cert head => cases sk; simp_all [marker,pos,metadata]
  cases c with
  | mk sk ch dat cert head =>
    simp_all [canonicalCell]
end Cell

namespace StructuralBlock
section
variable (B : StructuralBlock q)
def coreCell (i : Fin q) : Cell q := B.cores.get ⟨i.val,by rw [B.cores_length]; exact i.isLt⟩
omit [NeZero q] in
lemma coreCell_mem (i : Fin q) : B.coreCell i∈B.cores := List.get_mem _ _
omit [NeZero q] in
lemma coreCell_position (i : Fin q) : (B.coreCell i).pos=.core i := by
  have he := congrArg (fun l => l[i.val]?) B.core_positions
  simpa [List.getElem?_map,List.getElem?_eq_getElem,i.isLt,B.cores_length,coreCell,
    List.get_eq_getElem] using he

def bits (hd : d≤q) : Fin d → ZMod 2 :=
  fun j => (B.coreCell ⟨j.val,lt_of_lt_of_le j.isLt hd⟩).data false

lemma cores_canonical (hd : d≤q) (hf : ∀c∈B.cores,c.Format S d)
    (hm : ∀c∈B.cores,c.marker=.idle) :
    B.cores=(List.finRange q).map (fun p => canonicalCell (B.bits hd) (.core p)) := by
  apply List.ext_getElem (by simp [B.cores_length])
  intro i hi hi'
  let p : Fin q := ⟨i,by simpa [B.cores_length] using hi⟩
  have hc := Cell.core_idle_canonical (B.coreCell p) (B.bits hd) p
    (hf _ (B.coreCell_mem p)) (B.coreCell_position p) (hm _ (B.coreCell_mem p))
    (by intro h; rfl)
  simpa [coreCell,p,List.get_eq_getElem] using hc
end

variable (B : StructuralBlock q)
lemma core_ends : ∃ p c, B.cores=p++[c] ∧
    c.pos=.core (⟨q-1,Nat.sub_lt (NeZero.pos q) (by decide)⟩ : Fin q) := by
  let last : Fin q := ⟨q-1,Nat.sub_lt (NeZero.pos q) (by decide)⟩
  have he : B.cores.getLast?.map Cell.pos=some (.core last) := by
    rw [←List.getLast?_map,B.core_positions,List.getLast?_map,finRange_last]
    rfl
  obtain ⟨c,hc,hp⟩ := Option.map_eq_some_iff.mp he
  obtain ⟨p,hpc⟩ := List.getLast?_eq_some_iff.mp hc
  exact ⟨p,c,hpc,hp⟩

theorem normalize_idle (hd : d≤q) (hw : Survives S d B.word)
    (hm : ∀c∈B.word,c.marker=.idle) :
    Reach S d B.word (canonicalBlock (B.bits hd)) := by
  obtain ⟨p,c,hcores,hcp⟩ := B.core_ends
  have ht : q-1+1=q := by have := NeZero.pos q; omega
  have hwpal : Survives S d (c::B.palette++[B.stop]) :=
    hw.infix ⟨p,[],by simp [word,hcores,List.append_assoc]⟩
  have hroll := hwpal.checker_rollback hcp ht B.stop_position B.palette_positions
  have hpali : ∀a∈checkerIdle B.palette,a.isPalette := by
    simpa [checkerIdle] using B.palette_positions
  have hmi : ∀a∈checkerIdle B.palette,a.marker=.idle := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    exact hm b (by simp [word,hb])
  have hci : ∀a∈checkerIdle B.palette,a.checker=.idle := by simp [checkerIdle]
  have hpn : checkerIdle B.palette≠[] := by simpa [checkerIdle] using B.palette_nonempty
  obtain ⟨_,hpal⟩ := (hwpal.of_reach hroll).idle_palette_normalize hcp ht B.stop_position
    hpn hpali hmi hci (B.bits hd)
  have hr1 : Reach S d B.word (B.cores++checkerIdle B.palette++[B.stop]) := by
    simpa [word,hcores,List.append_assoc] using reach_context hroll p []
  have hr2 := reach_context hpal B.cores [B.stop]
  have hcanc := B.cores_canonical hd
    (fun c hc => hw.format (by simp [word,hc])) (fun c hc => hm c (by simp [word,hc]))
  have hstop := Cell.stop_idle_canonical B.stop (B.bits hd)
    (hw.format (by simp [word])) B.stop_position (hm _ (by simp [word]))
  have hfinal : B.cores++canonicalPalette (B.bits hd) (List.finRange q)++[B.stop]=
      canonicalBlock (B.bits hd) := by
    rw [hcanc,hstop]
    rfl
  rw [hfinal] at hr2
  exact hr1.trans hr2
end StructuralBlock

theorem idle_blocks_normalize (hd : d≤q) (bs : List (StructuralBlock q))
    (hw : Survives S d (bs.flatMap StructuralBlock.word))
    (hm : ∀c∈bs.flatMap StructuralBlock.word,c.marker=.idle) :
    Reach S d (bs.flatMap StructuralBlock.word) (encodeWord (bs.map (fun B => B.bits hd))) := by
  induction bs with
  | nil => exact .refl
  | cons B bs ih =>
    have hB : Survives S d B.word := hw.infix ⟨[],bs.flatMap StructuralBlock.word,by simp⟩
    have hbs : Survives S d (bs.flatMap StructuralBlock.word) := hw.infix ⟨B.word,[],by simp⟩
    have hmark : ∀c∈B.word,c.marker=.idle := fun c hc => hm c (by simp [hc])
    have hmarkbs : ∀c∈bs.flatMap StructuralBlock.word,c.marker=.idle :=
      fun c hc => hm c (by simp [hc])
    have h1 := reach_context (B.normalize_idle hd hB hmark) [] (bs.flatMap StructuralBlock.word)
    have h2 := reach_context (ih hbs hmarkbs) (canonicalBlock (B.bits hd)) []
    exact (by simpa [encodeWord,List.flatMap_cons] using h1.trans (by simpa [encodeWord] using h2))
end SourceBurnside.FiniteTable

end OAI
