import Mathlib
import OAI.GroupTheory.PeriodicGroups.Rules.PrefixRewriting

namespace OAI

universe u v w
namespace SourceBurnside.FiniteTable
section
open LocalSyntax LocalSyntax.Skeleton
variable {q d : ℕ} [NeZero q] {S : Schedule q}

omit [NeZero q] in
@[simp] lemma Cell.shape_core_iff (c : Cell q) (p : Fin q) :
    c.shape=.core p ↔ c.pos=.core p := by
  cases hp : c.pos <;> simp [shape,hp]
omit [NeZero q] in
@[simp] lemma Cell.shape_stop_iff (c : Cell q) : c.shape=.stop ↔ c.pos=.stop := by
  cases hp : c.pos <;> simp [shape,hp]

lemma startsCore_shape {v w : List (Cell q)} (he : v.map Cell.shape=w.map Cell.shape)
    (hv : StartsCore v) : StartsCore w := by
  have h : ∀s∈(v.map Cell.shape).head?,s=.core (0 : Fin q) := by
    simpa [List.head?_map,StartsCore] using hv
  rw [he] at h
  simpa [List.head?_map,StartsCore] using h

omit [NeZero q] in
lemma endsStop_shape {v w : List (Cell q)} (he : v.map Cell.shape=w.map Cell.shape)
    (hv : EndsStop v) : EndsStop w := by
  have h : ∀s∈(v.map Cell.shape).getLast?,s=.stop := by
    simpa [List.getLast?_map,EndsStop] using hv
  rw [he] at h
  simpa [List.getLast?_map,EndsStop] using h

theorem Survives.complete_normalize {w : List (Cell q)} (hw : Survives S d w)
    (hd : d≤q) (hs : Syntax S d w) (hfirst : StartsCore w) (hlast : EndsStop w) :
    ∃ u : List (Fin d → ZMod 2), Reach S d w (encodeWord u) := by
  obtain ⟨v,hv,hidle⟩ := hw.transactions_idle hs
  have hshape := reach_shape hv
  have hvc : StructuralChain v := (hw.of_reach hv).chain.imp (fun _ _ hp => hp.1.1)
  obtain ⟨bs,hbs⟩ := structural_decompose v hvc
    (startsCore_shape hshape hfirst) (endsStop_shape hshape hlast)
  refine ⟨bs.map (fun B => B.bits hd),hv.trans ?_⟩
  rw [hbs]
  exact idle_blocks_normalize hd bs (hbs ▸ (hw.of_reach hv)) (hbs ▸ hidle)

lemma Cell.cut_leftExternal {c : Cell q} (hc : c.Cut) (hf : c.Format S d) :
    c.skeleton.leftExternal := by
  rcases hc.2 with hi|hb
  · exact Or.inl hi
  · have hfirst : c.skeleton.first := ⟨hb,0,hc.1,rfl⟩
    exact Or.inr ⟨fun hr => hf.1.1 hr hfirst,hfirst⟩

lemma pair_before_core_zero {a b : Cell q} (hp : Pair a b)
    (hb : b.pos=.core (0 : Fin q)) : a.pos=.stop := by
  have h := hp.1.1
  change b.skeleton.pos=.core (0 : Fin q) at hb
  cases ha : a.pos with
  | core p =>
    change a.skeleton.pos=.core p at ha
    simp only [Skeleton.Structural,ha,hb,Fin.val_zero] at h
    omega
  | palette x =>
    change a.skeleton.pos=.palette x at ha
    simp only [Skeleton.Structural,ha,hb] at h
  | stop => rfl

lemma Survives.syntax_of_exterior {w : List (Cell q)} (hw : Survives S d w)
    (hl : ∀a∈w.head?,a.skeleton.leftExternal)
    (hr : ∀a∈w.getLast?,a.skeleton.rightExternal) : Syntax S d w := by
  refine ⟨⟨?_,?_⟩,hw.chain.imp (fun _ _ h => h.2),fun a ha => hw.format ha⟩
  · intro a ha
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ha
    exact (hw.format hc).1
  · have hp : (w.map (fun a : Cell q => some a.skeleton)).IsChain Skeleton.Link := by
      rw [List.isChain_map]
      exact hw.chain.imp (fun _ _ h => h.1)
    have hlast : ∀a∈(w.map (fun a : Cell q => some a.skeleton)).getLast?,
        ∀b∈([none] : List (Option (Skeleton q 10))).head?,Skeleton.Link a b := by
      simpa [List.getLast?_map,Skeleton.Link] using hr
    have htail : ((w.map (fun a : Cell q => some a.skeleton))++[none]).IsChain Skeleton.Link :=
      List.isChain_append.mpr ⟨hp,by simp,hlast⟩
    rw [List.isChain_cons]
    refine ⟨?_,by simpa [List.map_map,Function.comp_def] using htail⟩
    cases w with
    | nil => simp [Skeleton.Link]
    | cons a w => simpa [Skeleton.Link] using hl a (by simp)

lemma Survives.before_cut_end {w : List (Cell q)} {b : Cell q}
    (hw : Survives S d (w++[b])) (hb : b.Cut) :
    EndsStop w ∧ ∀a∈w.getLast?,a.skeleton.rightExternal := by
  have hbext := Cell.cut_leftExternal hb (hw.format (by simp))
  have hedge := (List.isChain_append.mp hw.chain).2.2
  constructor
  · intro a ha
    exact pair_before_core_zero (hedge a ha b (by simp)) hb.1
  · intro a ha
    rcases (hedge a ha b (by simp)).1.2 with he|hi
    · exact he.1
    · exact (hi.2.1 hbext).elim

theorem Survives.cut_interval_normalize {a b : Cell q} {w : List (Cell q)}
    (hw : Survives S d (a::w++[b])) (ha : a.Cut) (hb : b.Cut) (hd : d≤q) :
    ∃ u : List (Fin d → ZMod 2), Reach S d (a::w) (encodeWord u) := by
  have hw' : Survives S d (a::w) := hw.infix ⟨[],[b],by simp⟩
  have hedge := hw.before_cut_end hb
  have hsyntax := hw'.syntax_of_exterior
    (by simpa using Cell.cut_leftExternal ha (hw'.format (by simp))) hedge.2
  exact hw'.complete_normalize hd hsyntax (by simpa [StartsCore] using ha.1) hedge.1
end

section
open LocalSyntax LocalSyntax.Skeleton
variable {q d : ℕ} [NeZero q] {S : Schedule q}

def GeomRel (a b : Cell q) : Prop := a.geometryRank≤b.geometryRank ∧
  (a.geometryRank=b.geometryRank → a.isPalette ∧ b.isPalette)

instance : Trans (GeomRel (q:=q)) GeomRel GeomRel where
  trans := by
    intro a b c hab hbc
    have habL := hab.1
    have hbcL := hbc.1
    refine ⟨habL.trans hbcL,?_⟩
    intro he
    have hab' : a.geometryRank=b.geometryRank := by omega
    have hbc' : b.geometryRank=c.geometryRank := by omega
    exact ⟨(hab.2 hab').1,(hbc.2 hbc').2⟩

lemma Survives.geom_rel {w : List (Cell q)} (hw : Survives S d w)
    (hn : ∀c∈w.tail,¬c.Cut) : w.Pairwise GeomRel := by
  suffices w.IsChain GeomRel from this.pairwise
  induction w with
  | nil => simp
  | cons a w ih =>
    cases w with
    | nil => simp
    | cons b w =>
      refine List.isChain_cons_cons.mpr ⟨?_,?_⟩
      · exact pair_noCut_geometry (hw.pair ⟨[],w,by simp⟩) (hn b (by simp))
      · exact ih (hw.infix ⟨[a],[],by simp⟩) (fun c hc => hn c (List.mem_cons_of_mem b hc))

def beginnings (w : List (Cell q)) : List (Cell q) :=
  w.filter (fun c => decide (c.pos=.core (0 : Fin q)))
def firstCoreCount (w : List (Cell q)) : ℕ := (beginnings w).length

lemma Survives.beginning_ranks {w : List (Cell q)} (hw : Survives S d w)
    (hn : ∀c∈w.tail,¬c.Cut) : ((beginnings w).map Cell.blockRank).Pairwise (· < ·) := by
  rw [List.pairwise_map]
  apply ((hw.geom_rel hn).filter _).imp_of_mem
  intro a b ha hb hab
  have hpa : a.pos=.core (0 : Fin q) := by simpa [beginnings] using (List.mem_filter.mp ha).2
  have hpb : b.pos=.core (0 : Fin q) := by simpa [beginnings] using (List.mem_filter.mp hb).2
  have hne : a.geometryRank≠b.geometryRank := by
    intro he
    obtain ⟨x,hx⟩ := (hab.2 he).1
    rw [hpa] at hx
    cases hx
  have hlt : a.geometryRank<b.geometryRank := lt_of_le_of_ne hab.1 hne
  simpa [Cell.geometryRank,Cell.positionRank,hpa,hpb] using hlt

lemma rank_list_bound {l : List ℕ} (h : l.Pairwise (· < ·))
    (hb : ∀n∈l.tail,n<10) : l.length≤10 := by
  cases l with
  | nil => simp
  | cons a l =>
    cases l with
    | nil => simp
    | cons b l =>
      have ha : a<10 := lt_trans ((List.pairwise_cons.mp h).1 b (by simp)) (hb b (by simp))
      have hall : ∀n∈a::b::l,n<10 := by
        intro n hn
        rcases List.mem_cons.mp hn with rfl|hn
        · exact ha
        · exact hb n hn
      have hc : (a::b::l).toFinset ⊆ Finset.range 10 := by
        intro n hn
        exact Finset.mem_range.mpr (hall n (List.mem_toFinset.mp hn))
      have he := Finset.card_le_card hc
      rw [List.toFinset_card_of_nodup h.nodup,Finset.card_range] at he
      exact he

lemma Survives.beginning_count_bound {w : List (Cell q)} (hw : Survives S d w)
    (hn : ∀c∈w.tail,¬c.Cut) : firstCoreCount w≤10 := by
  have hb : ∀c∈(beginnings w).tail,c.blockRank<10 := by
    intro c hc
    have hc' : c∈w.tail := by
      cases w with
      | nil => simp [beginnings] at hc
      | cons a w =>
        by_cases ha : a.pos=.core (0 : Fin q)
        · exact (by simpa [beginnings,ha] using hc : c∈w ∧ c.pos=.core (0 : Fin q)).1
        · have hct : c∈(beginnings w).tail := by simpa [beginnings,ha] using hc
          exact (List.mem_filter.mp (List.mem_of_mem_tail hct)).1
    have hp : c.pos=.core (0 : Fin q) := (of_decide_eq_true (List.mem_filter.mp
      (List.mem_of_mem_tail hc)).2)
    have hm : c.marker≠.idle := fun hm => hn c hc' ⟨hp,Or.inl hm⟩
    exact c.blockRank_lt_ten hm
  have hh := rank_list_bound (hw.beginning_ranks hn) (by simpa [←List.map_tail] using hb)
  simpa [firstCoreCount] using hh

lemma firstCoreCount_eq (w : List (Cell q)) : firstCoreCount w=
    w.countP (fun c => decide (c.pos=.core (0 : Fin q))) := by
  simp [firstCoreCount,beginnings,List.countP_eq_length_filter]

lemma firstCoreCount_shape (w : List (Cell q)) : firstCoreCount w=
    (w.map Cell.shape).countP (fun s => decide (s=.core (0 : Fin q))) := by
  rw [firstCoreCount_eq,List.countP_map]
  apply congrArg (fun f => w.countP f)
  funext c
  cases hp : c.pos <;> simp [Cell.shape,hp]

lemma firstCoreCount_reach {v w : List (Cell q)} (hr : Reach S d v w) :
    firstCoreCount v=firstCoreCount w := by
  rw [firstCoreCount_shape,firstCoreCount_shape,reach_shape hr]

@[simp] lemma firstCoreCount_append (v w : List (Cell q)) :
    firstCoreCount (v++w)=firstCoreCount v+firstCoreCount w := by
  simp [firstCoreCount_eq,List.countP_append]

@[simp] lemma firstCoreCount_block (bits : Fin d → ZMod 2) :
    firstCoreCount (canonicalBlock (q:=q) bits)=1 := by
  simp only [firstCoreCount,beginnings,canonicalBlock,List.filter_append,
    List.filter_map,List.length_append,List.length_map]
  simp [canonicalCell,Function.comp_def,Cell.pos,List.filter_eq,
    List.count_eq_one_of_mem (List.nodup_finRange q) (List.mem_finRange (0 : Fin q))]

@[simp] lemma firstCoreCount_encode (u : List (Fin d → ZMod 2)) :
    firstCoreCount (encodeWord (q:=q) u)=u.length := by
  induction u with
  | nil => simp [firstCoreCount,beginnings,encodeWord]
  | cons a u ih => simpa [encodeWord,Nat.add_comm] using ih
end

section
open LocalSyntax LocalSyntax.Skeleton
variable {q d : ℕ} [NeZero q] {S : Schedule q}

theorem Survives.token_normalization {a b : Cell q} {w : List (Cell q)}
    (hw : Survives S d (a::w++[b])) (ha : a.Cut) (hb : b.Cut)
    (hn : ∀c∈w,¬c.Cut) (hd : d≤q) :
    ∃ u : List (Fin d → ZMod 2), 1≤u.length ∧ u.length≤10 ∧
      (a::w).length=(2*q+1)*u.length ∧ Reach S d (a::w) (encodeWord u) := by
  obtain ⟨u,hr⟩ := hw.cut_interval_normalize ha hb hd
  have hl : (a::w).length=(2*q+1)*u.length := by
    simpa using reach_length hr
  have hu : 1≤u.length := by
    by_contra h
    have hz : u.length=0 := by omega
    simp [hz] at hl
  have hw' : Survives S d (a::w) := hw.infix ⟨[],[b],by simp⟩
  have hc := hw'.beginning_count_bound hn
  rw [firstCoreCount_reach hr,firstCoreCount_encode] at hc
  exact ⟨u,hu,hc,hl,hr⟩
end

open LocalSyntax LocalSyntax.Skeleton
namespace Rigid
variable {q d n : ℕ} [NeZero q]

def width (q : ℕ) := 2*q+1
omit [NeZero q] in
lemma width_pos : 0<width q := by simp [width]

def position (i : Fin (width q)) : Position q :=
  if hi : i.val<q then .core ⟨i.val,hi⟩
  else if hp : i.val<2*q then .palette ⟨i.val-q,by omega⟩ else .stop

def shape (i : Fin (width q)) : Shape q := match position i with
  | .core p => .core p | .palette _ => .palette | .stop => .stop

def coord (i : Fin (n*width q)) : Fin (width q) :=
  ⟨i.val%width q,Nat.mod_lt _ width_pos⟩
def block (i : Fin (n*width q)) : Fin n :=
  ⟨i.val/width q,(Nat.div_lt_iff_lt_mul width_pos).mpr i.isLt⟩
def cell (b : Fin n) (p : Fin (width q)) : Fin (n*width q) :=
  ⟨b.val*width q+p.val,by
    have hh := Nat.mul_le_mul_right (width q) (show b.val+1≤n from b.isLt)
    have hp := p.isLt
    nlinarith⟩
def core (b : Fin n) (p : Fin q) : Fin (n*width q) := cell b ⟨p.val,by
  have := p.isLt; simp [width]; omega⟩

omit [NeZero q] in
lemma coord_cell (b : Fin n) (p : Fin (width q)) : coord (cell b p)=p := by
  apply Fin.ext
  simp [coord,cell,Nat.add_mod,Nat.mod_eq_of_lt p.isLt]
omit [NeZero q] in
lemma block_cell (b : Fin n) (p : Fin (width q)) : block (cell b p)=b := by
  apply Fin.ext
  change (b.val*width q+p.val)/width q=b.val
  rw [Nat.add_comm,Nat.add_mul_div_right _ _ width_pos,Nat.div_eq_of_lt p.isLt]
  simp
omit [NeZero q] in
lemma cell_block_coord (i : Fin (n*width q)) : cell (block i) (coord i)=i := by
  apply Fin.ext
  simpa [cell,block,coord,Nat.mul_comm] using Nat.div_add_mod i.val (width q)

omit [NeZero q] in
lemma position_core_iff (i : Fin (width q)) (p : Fin q) :
    position i=.core p ↔ i.val=p.val := by
  unfold position
  split_ifs with hi hp
  · simp only [Position.core.injEq,Fin.ext_iff]
  · simp only [false_iff]
    intro he; have := p.isLt; omega
  · simp only [false_iff]
    intro he; have := p.isLt; omega
omit [NeZero q] in
lemma position_stop_iff (i : Fin (width q)) : position i=.stop ↔ i.val=2*q := by
  have := i.isLt
  unfold width at this
  unfold position
  split_ifs <;> simp_all only [false_iff,true_iff] <;> omega
omit [NeZero q] in
lemma shape_core_iff (i : Fin (width q)) (p : Fin q) :
    shape i=.core p ↔ i.val=p.val := by
  rw [←position_core_iff]
  cases hp : position i <;> simp [shape,hp]
omit [NeZero q] in
lemma shape_stop_iff (i : Fin (width q)) : shape i=.stop ↔ i.val=2*q := by
  rw [←position_stop_iff]
  cases hp : position i <;> simp [shape,hp]

lemma canonicalBlock_get (bits : Fin d → ZMod 2) (i : Fin (width q)) :
    (canonicalBlock (q:=q) bits)[i.val]'(by simpa [width] using i.isLt)=
      canonicalCell bits (position i) := by
  have hi := i.isLt
  unfold width at hi
  by_cases hc : i.val<q
  · simp [canonicalBlock,position,hc]
  · by_cases hp : i.val<2*q
    · have hr : i.val-q<q := by omega
      simp [canonicalBlock,List.getElem_append,position,hc,hp,hr]
    · have he : i.val=2*q := by omega
      simp [canonicalBlock,List.getElem_append,position,he,show ¬2*q<q by omega,show ¬2*q-q<q by omega]

lemma canonicalBlock_ofFn (bits : Fin d → ZMod 2) :
    canonicalBlock (q:=q) bits=List.ofFn (fun i : Fin (width q) =>
      canonicalCell bits (position i)) := by
  apply List.ext_getElem
  · simp [width]
  · intro i hi hj
    simpa using canonicalBlock_get bits ⟨i,by simpa [width] using hi⟩

def encoded (u : Fin n → Fin d → ZMod 2) (i : Fin (n*width q)) : Cell q :=
  canonicalCell (u (block i)) (position (coord i))

lemma encoded_cell (u : Fin n → Fin d → ZMod 2) (b : Fin n) (p : Fin (width q)) :
    encoded u (cell b p)=canonicalCell (u b) (position p) := by
  simp [encoded,block_cell,coord_cell]

lemma encoded_ofFn (u : Fin n → Fin d → ZMod 2) :
    List.ofFn (encoded (q:=q) u)=encodeWord (List.ofFn u) := by
  rw [List.ofFn_mul]
  simp only [encodeWord,List.flatMap_def,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext b
  simp only [Function.comp_def]
  rw [canonicalBlock_ofFn]
  apply congrArg List.ofFn
  funext p
  exact encoded_cell u b p

def Layout (f : Fin (n*width q) → Cell q) : Prop := ∀i, (f i).shape=shape (coord i)

lemma layout_encoded (u : Fin n → Fin d → ZMod 2) : Layout (encoded (q:=q) u) := by
  intro i
  unfold encoded Cell.shape shape
  rw [canonicalCell_pos]
  rfl

noncomputable def decoded (hd : d≤q) (f : Fin (n*width q) → Cell q) :
    Fin n → Fin d → ZMod 2 := fun b p => Committed.value f (core b (p.castLE hd))

omit [NeZero q] in
lemma decoded_eq {hd : d≤q} {f g : Fin (n*width q) → Cell q}
    (h : ∀i,Committed.value f i=Committed.value g i) : decoded hd f=decoded hd g := by
  funext b p
  exact h _

lemma decoded_encoded (hd : d≤q) (u : Fin n → Fin d → ZMod 2) :
    decoded hd (encoded (q:=q) u)=u := by
  funext b p
  rw [decoded,Committed.idle (by simp [encoded])]
  rw [core,encoded_cell]
  have hp : position (⟨(p.castLE hd).val,by have := (p.castLE hd).isLt; simp [width]; omega⟩ :
      Fin (width q))=.core (p.castLE hd) := (position_core_iff _ _).mpr rfl
  rw [hp]
  simp [canonicalCell,p.isLt]

omit [NeZero q] in
lemma layout_core {f : Fin (n*width q) → Cell q} (hf : Layout f) (b : Fin n) (p : Fin q) :
    (f (core b p)).pos=.core p := by
  apply (Cell.shape_core_iff _ _).mp
  rw [hf,core,coord_cell]
  exact (shape_core_iff _ _).mpr rfl
omit [NeZero q] in
lemma layout_core_iff {f : Fin (n*width q) → Cell q} (hf : Layout f)
    (i : Fin (n*width q)) (p : Fin q) :
    (f i).pos=.core p ↔ i.val%width q=p.val := by
  rw [←Cell.shape_core_iff,hf,shape_core_iff]
  rfl
omit [NeZero q] in
lemma layout_stop_iff {f : Fin (n*width q) → Cell q} (hf : Layout f)
    (i : Fin (n*width q)) : (f i).pos=.stop ↔ i.val%width q=2*q := by
  rw [←Cell.shape_stop_iff,hf,shape_stop_iff]
  rfl

lemma layout_reach {S : Schedule q} {f g : Fin (n*width q) → Cell q}
    (hf : Layout f) (hr : Reach S d (List.ofFn f) (List.ofFn g)) : Layout g := by
  have he := reach_shape hr
  simp only [List.map_ofFn] at he
  have he' := List.ofFn_injective he
  intro i
  exact (congrFun he' i).symm.trans (hf i)

omit [NeZero q] in
lemma block_mono {i j : Fin (n*width q)} (h : i≤j) : block i≤block j :=
  Nat.div_le_div_right h

lemma block_next {i j : Fin (n*width q)} (h : i.val+1=j.val) :
    (block j).val=(block i).val+if i.val%width q=2*q then 1 else 0 := by
  change j.val/width q=i.val/width q+_
  rw [←h]
  have h1 : 1<width q := by have := NeZero.pos q; dsimp [width]; omega
  by_cases ht : i.val%width q=2*q
  · have hz : (i.val+1)%width q=0 := by
      rw [Nat.add_mod,Nat.mod_eq_of_lt h1,ht]
      exact Nat.mod_self (2*q+1)
    rw [ite_eq_left ht,Nat.succ_div_of_mod_eq_zero hz]
  · have hk : i.val%width q+1<width q := by
      have := Nat.mod_lt i.val (width_pos (q:=q))
      unfold width at *
      omega
    have hz : (i.val+1)%width q≠0 := by
      rw [Nat.add_mod,Nat.mod_eq_of_lt h1,Nat.mod_eq_of_lt hk]
      omega
    rw [ite_eq_right ht,Nat.succ_div_of_mod_ne_zero hz,Nat.add_zero]

omit [NeZero q] in
lemma first_le_iff (b : Fin n) (j : Fin (n*width q)) :
    cell b ⟨0,width_pos⟩≤j ↔ b≤block j := by
  constructor
  · intro h
    simpa only [block_cell] using block_mono h
  · intro h
    have hm := Nat.mul_le_mul_right (width q) h
    have he := congrArg Fin.val (cell_block_coord j)
    change b.val*width q+0≤j.val
    change (block j).val*width q+(coord j).val=j.val at he
    omega
omit [NeZero q] in
lemma le_last_iff (b : Fin n) (j : Fin (n*width q)) :
    j≤cell b ⟨2*q,by simp [width]⟩ ↔ block j≤b := by
  constructor
  · intro h
    simpa only [block_cell] using block_mono h
  · intro h
    have hm := Nat.mul_le_mul_right (width q) h
    have he := congrArg Fin.val (cell_block_coord j)
    change j.val≤b.val*width q+2*q
    change (block j).val*width q+(coord j).val=j.val at he
    have hp : (coord j).val≤2*q := by have := (coord j).isLt; unfold width at this; omega
    omega

section Component
variable {S : Schedule q} {f : Fin (n*width q) → Cell q} (hl : Layout f)
  (hs : Syntax S d (List.ofFn f)) (i : Fin (n*width q)) (hi : (f i).marker=.full)
include hl hs hi

lemma component_left_mod : (Component.left f i).val%width q=0 := by
  obtain ⟨_,p,hp,hz⟩ := Component.first f i (Verification.coherent_of_syntax S hs)
    (exterior_of_syntax hs) (Or.inr hi)
  change (f (Component.left f i)).pos=.core p at hp
  rw [layout_core_iff hl _ _] at hp
  omega
lemma component_right_mod : (Component.right f i).val%width q=2*q := by
  exact (layout_stop_iff hl _).mp (Component.last f i (Verification.coherent_of_syntax S hs)
    (exterior_of_syntax hs) hi).2

lemma component_left_cell : Component.left f i=cell (block (Component.left f i)) ⟨0,width_pos⟩ := by
  have hh := cell_block_coord (Component.left f i)
  have hc : coord (Component.left f i)=⟨0,width_pos⟩ := Fin.ext (component_left_mod hl hs i hi)
  rw [hc] at hh
  exact hh.symm
lemma component_right_cell : Component.right f i=cell (block (Component.right f i))
    ⟨2*q,by simp [width]⟩ := by
  have hh := cell_block_coord (Component.right f i)
  have hc : coord (Component.right f i)=⟨2*q,by simp [width]⟩ :=
    Fin.ext (component_right_mod hl hs i hi)
  rw [hc] at hh
  exact hh.symm

lemma component_block_counter (j : Fin (Component.size f i)) :
    (f (Component.offset f i j)).metadata.block.val+(block (Component.left f i)).val=
      (block (Component.offset f i j)).val := by
  generalize he : j.val=t
  induction t generalizing j with
  | zero =>
    have ho : Component.offset f i j=Component.left f i := by apply Fin.ext; simp [Component.offset,he]
    rw [ho]
    have hh := (Component.first f i (Verification.coherent_of_syntax S hs)
      (exterior_of_syntax hs) (Or.inr hi)).1
    simp only [Cell.metadata] at *
    omega
  | succ t ih =>
    let p : Fin (Component.size f i) := ⟨t,by have := j.isLt; omega⟩
    have hpj : p.val+1=j.val := by dsimp [p]; omega
    have ih' := ih p rfl
    have hj := Component.offset_adjacent f i p j hpj
    have hb := block_next hj
    have hh := (Component.offset_internal f i (Verification.coherent_of_syntax S hs)
      p j hpj).2.2.1
    change (if (f (Component.offset f i p)).pos=.stop then
      (f (Component.offset f i p)).metadata.block.val+1=(f (Component.offset f i j)).metadata.block.val
      else (f (Component.offset f i p)).metadata.block.val=(f (Component.offset f i j)).metadata.block.val) at hh
    by_cases hp : (f (Component.offset f i p)).pos=.stop
    · rw [ite_eq_left hp] at hh
      rw [ite_eq_left ((layout_stop_iff hl _).mp hp)] at hb
      change (f (Component.offset f i p)).metadata.block.val+1=
        (f (Component.offset f i j)).metadata.block.val at hh
      omega
    · rw [ite_eq_right hp] at hh
      rw [ite_eq_right (by simpa only [←layout_stop_iff hl _] using hp)] at hb
      change (f (Component.offset f i p)).metadata.block.val=
        (f (Component.offset f i j)).metadata.block.val at hh
      omega

lemma component_last_block : (block (Component.right f i)).val=
    (block (Component.left f i)).val+(f i).metadata.arity.val := by
  obtain ⟨j,hj⟩ := Component.offset_surjective f i (Component.connected_right f i)
  have hh := component_block_counter hl hs i hi j
  rw [hj] at hh
  have hs' := (Component.last f i (Verification.coherent_of_syntax S hs)
    (exterior_of_syntax hs) hi).1
  have ht := SameRegion.task (Verification.coherent_of_syntax S hs)
    (Component.connected_right f i)
  have ha := congrArg (fun t : Task => t.arity.val) ht
  change (f i).metadata.arity.val=(f (Component.right f i)).metadata.arity.val at ha
  change (f (Component.right f i)).metadata.block.val=(f (Component.right f i)).metadata.arity.val at hs'
  omega

lemma component_interval (j : Fin (n*width q)) : SameRegion f i j ↔
    (block (Component.left f i)).val≤(block j).val ∧
      (block j).val<(block (Component.left f i)).val+(f i).metadata.arity.val+1 := by
  rw [Component.interval,component_left_cell hl hs i hi,component_right_cell hl hs i hi,
    first_le_iff,le_last_iff]
  change (block (Component.left f i)).val≤(block j).val ∧
    (block j).val≤(block (Component.right f i)).val ↔ _
  rw [component_last_block hl hs i hi]
  simp only [block_cell]
  omega

lemma component_size : Component.size f i=((f i).metadata.arity.val+1)*width q := by
  unfold Component.size
  have hh := component_last_block hl hs i hi
  have hleft := congrArg Fin.val (component_left_cell hl hs i hi)
  have hright := congrArg Fin.val (component_right_cell hl hs i hi)
  change (Component.left f i).val=(block (Component.left f i)).val*width q+0 at hleft
  change (Component.right f i).val=(block (Component.right f i)).val*width q+2*q at hright
  rw [hleft,hright,hh]
  simp only [Nat.add_zero,Nat.add_mul,Nat.one_mul]
  dsimp [width]
  omega

noncomputable def regionBlock (b : Fin ((f i).metadata.arity.val+1)) : Fin n :=
  ⟨(block (Component.left f i)).val+b.val,by
    have hh := component_last_block hl hs i hi
    have hb := b.isLt
    have hr := (block (Component.right f i)).isLt
    omega⟩

lemma regionCore_owned (b : Fin ((f i).metadata.arity.val+1)) (p : Fin q) :
    SameRegion f i (core (regionBlock hl hs i hi b) p) := by
  rw [component_interval hl hs i hi]
  simp only [core,block_cell,regionBlock]
  have := b.isLt
  omega

lemma region_cell (b : Fin ((f i).metadata.arity.val+1)) (p : Fin q) :
    let R := Component.region f i hs hi
    R.cell (R.locate b p)=f (core (regionBlock hl hs i hi b) p) := by
  intro R
  obtain ⟨j,hj⟩ := Component.offset_surjective f i (regionCore_owned hl hs i hi b p)
  have hc : (R.cell j).pos=.core p := by
    change (f (Component.offset f i j)).pos=.core p
    rw [hj]
    exact layout_core hl _ _
  have hb : (R.cell j).metadata.block.val=b.val := by
    have hh := component_block_counter hl hs i hi j
    rw [hj] at hh
    rw [show block (core (regionBlock hl hs i hi b) p)=regionBlock hl hs i hi b from block_cell _ _] at hh
    change (f (core (regionBlock hl hs i hi b) p)).metadata.block.val+
      (block (Component.left f i)).val=(block (Component.left f i)).val+b.val at hh
    change (f (Component.offset f i j)).metadata.block.val=b.val
    rw [hj]
    omega
  have he := R.locate_unique b p j hb hc
  rw [←he]
  exact congrArg f hj

end Component

lemma split_ofFn {α : Type*} (f : Fin n → α) (a k : ℕ) (h : a+k≤n) :
    List.ofFn f =
      List.ofFn (fun i : Fin a => f ⟨i.val,by have := i.isLt; omega⟩) ++
      List.ofFn (fun i : Fin k => f ⟨a+i.val,by have := i.isLt; omega⟩) ++
      List.ofFn (fun i : Fin (n-(a+k)) => f ⟨a+k+i.val,by have := i.isLt; omega⟩) := by
  apply List.ext_getElem
  · simp; omega
  · intro i hi hj
    simp only [List.length_append,List.length_ofFn,List.getElem_append,List.getElem_ofFn]
    split_ifs <;> apply congrArg f <;> apply Fin.ext <;> dsimp only <;> omega

lemma context_of_interval {α : Type*} (f g : Fin n → α) (a k : ℕ) (h : a+k≤n)
    (u v : Fin k → α)
    (hu : ∀ i : Fin k, f ⟨a+i.val,by have := i.isLt; omega⟩=u i)
    (hv : ∀ i : Fin k, g ⟨a+i.val,by have := i.isLt; omega⟩=v i)
    (ho : ∀ i : Fin n, ¬(a ≤ i.val ∧ i.val < a+k) → f i=g i) :
    ∃ p s : List α, List.ofFn f=p++List.ofFn u++s ∧ List.ofFn g=p++List.ofFn v++s := by
  refine ⟨List.ofFn (fun i : Fin a => f ⟨i.val,by have := i.isLt; omega⟩),
    List.ofFn (fun i : Fin (n-(a+k)) => f ⟨a+k+i.val,by have := i.isLt; omega⟩),?_,?_⟩
  · rw [split_ofFn f a k h]
    simp only [hu]
  · rw [split_ofFn g a k h]
    simp only [hv]
    congr 2
    · apply congrArg List.ofFn
      funext i
      symm
      apply ho
      have := i.isLt
      dsimp only
      omega
    · funext i
      symm
      apply ho
      dsimp only
      omega

theorem pivot_context {S : Schedule q} {f g : Fin (n*width q) → Cell q}
    (hd : d≤q) (hl : Layout f) (hs : Syntax S d (List.ofFn f))
    (ht : Syntax S d (List.ofFn g)) {i : Fin (n*width q)} (hp : Committed.PivotAt f g i) :
    ∃ (hi : (f i).marker=.full) (s : Bool) (p t : List (Fin d → ZMod 2)),
      let R := Component.region f i hs hi
      (f i).metadata.zeroTask=false ∧ (f i).head.phase=.success ∧
      List.ofFn (decoded hd f)=p++List.ofFn (fun b p => R.slot s b (p.castLE hd))++t ∧
      List.ofFn (decoded hd g)=p++List.ofFn (fun b p => R.slot (!s) b (p.castLE hd))++t := by
  obtain ⟨a,s,hfi,hgi,hoff,hlast,hzero⟩ := hp
  have hi : (f i).marker=.full := by simp [hfi,Cell.full,Cell.marker,Skeleton.mark]
  let R := Component.region f i hs hi
  have hp : Committed.PivotAt f g i := ⟨a,s,hfi,hgi,hoff,hlast,hzero⟩
  have hv := Committed.pivot (Verification.coherent_of_syntax S hs)
    (Verification.coherent_of_syntax S ht) (hp.unary (S:=S)) hfi hgi
  have hfslot (b : Fin ((f i).metadata.arity.val+1)) (p : Fin d) :
      decoded hd f (regionBlock hl hs i hi b) p=R.slot s b (p.castLE hd) := by
    rw [decoded,hv.1 _ (Connected.symm (regionCore_owned hl hs i hi b (p.castLE hd)))]
    change _ = (R.cell (R.locate b (p.castLE hd))).data _
    rw [region_cell hl hs i hi]
  have hgslot (b : Fin ((f i).metadata.arity.val+1)) (p : Fin d) :
      decoded hd g (regionBlock hl hs i hi b) p=R.slot (!s) b (p.castLE hd) := by
    rw [decoded,hv.2,ite_eq_left (Connected.symm (regionCore_owned hl hs i hi b (p.castLE hd)))]
    change _ = (R.cell (R.locate b (p.castLE hd))).data _
    rw [region_cell hl hs i hi]
  have hb : (block (Component.left f i)).val+((f i).metadata.arity.val+1)≤n := by
    have hh := component_last_block hl hs i hi
    have hr := (block (Component.right f i)).isLt
    omega
  obtain ⟨p,t,hf,hg⟩ := context_of_interval (decoded hd f) (decoded hd g)
    (block (Component.left f i)).val ((f i).metadata.arity.val+1) hb
    (fun b p => R.slot s b (p.castLE hd)) (fun b p => R.slot (!s) b (p.castLE hd))
    (fun b => funext (hfslot b)) (fun b => funext (hgslot b)) (by
      intro b hbo
      funext p
      rw [decoded,decoded,hv.2,ite_eq_right]
      intro ho
      have hh := (component_interval hl hs i hi (core b (p.castLE hd))).mp ho.symm
      simp only [core,block_cell] at hh
      exact hbo (by simpa [Nat.add_assoc] using hh))
  refine ⟨hi,s,p,t,?_,?_,hf,hg⟩
  · simpa [hfi,Cell.full,Cell.metadata,Skeleton.mark] using hzero
  · simp [hfi,Cell.full]

end Rigid
end SourceBurnside.FiniteTable

end OAI
