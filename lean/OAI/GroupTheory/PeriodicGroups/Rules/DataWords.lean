import Mathlib
import OAI.GroupTheory.PeriodicGroups.Rules.GeometricRelations

namespace OAI

universe u v w
namespace SourceBurnside.FiniteTable
section
open LocalSyntax LocalSyntax.Skeleton
variable {q d n : ℕ} [NeZero q]
namespace Region
noncomputable def dataWord (R : Region q d) (hd : d≤q) (s : Bool) : List (Fin d → ZMod 2) :=
  List.ofFn (fun b p => R.slot s b (p.castLE hd))
end Region

inductive CheckedSwap (S : Schedule q) (hd : d≤q) : List (Fin d → ZMod 2) → List (Fin d → ZMod 2) → Prop
  | mk (R : Region q d) (s : Bool) (hz : R.task.zeroTask=false)
      (hc : ∀j,(R.plan S).Holds j) (p t : List (Fin d → ZMod 2)) :
      CheckedSwap S hd (p++R.dataWord hd s++t) (p++R.dataWord hd (!s)++t)

def CheckedZero (S : Schedule q) (hd : d≤q) (w : List (Fin d → ZMod 2)) : Prop :=
  ∃ (R : Region q d) (p t : List (Fin d → ZMod 2)), R.task.zeroTask=true ∧
    (∀j,(R.plan S).Holds j) ∧ w=p++R.dataWord hd false++t

def CheckedReach (S : Schedule q) (hd : d≤q) := Relation.ReflTransGen (CheckedSwap S hd)

namespace Rigid
lemma decoded_step {S : Schedule q} {f g : Fin (n*width q) → Cell q}
    (hd : d≤q) (hl : Layout f) (hs : Syntax S d (List.ofFn f))
    (hg : Verification.AllGood S f) (he : Step S d (List.ofFn f) (List.ofFn g)) :
    CheckedReach S hd (List.ofFn (decoded hd f)) (List.ofFn (decoded hd g)) := by
  obtain hz|⟨i,hp⟩ := Committed.step_classified hs he
  · rw [decoded_eq hz]
    exact .refl
  · have ht := reach_syntax (Relation.ReflTransGen.single he) hs
    obtain ⟨hi,s,p,t,hzero,hphase,hf,hg'⟩ := pivot_context hd hl hs ht hp
    have hc := Component.region_holds f i hs hi (hg i hi) hphase
    rw [hf,hg']
    exact .single (.mk (Component.region f i hs hi) s hzero hc p t)

theorem decoded_reach {S : Schedule q} (hd : d≤q) {f g : Fin (n*width q) → Cell q}
    (hl : Layout f) (hs : Syntax S d (List.ofFn f)) (hg : Verification.AllGood S f)
    (hr : Reach S d (List.ofFn f) (List.ofFn g)) :
    CheckedReach S hd (List.ofFn (decoded hd f)) (List.ofFn (decoded hd g)) := by
  generalize he : List.ofFn g=w at hr
  induction hr generalizing g with
  | refl =>
    have hfg : f=g := List.ofFn_injective he.symm
    subst g
    exact .refl
  | @tail v w h e ih =>
    have hvlen : v.length=n*width q := by
      have hh := reach_length h
      simpa using hh.symm
    let mid : Fin (n*width q) → Cell q := fun i => v.get (Fin.cast hvlen.symm i)
    have hm : List.ofFn mid=v := by
      rw [show mid=(fun i => v.get (Fin.cast hvlen.symm i)) from rfl,
        ←List.ofFn_congr hvlen v.get]
      exact List.ofFn_get v
    have hmreach : Reach S d (List.ofFn f) (List.ofFn mid) := by rwa [hm]
    have hmstep : Step S d (List.ofFn mid) (List.ofFn g) := by rwa [hm,he]
    have hmgood : Verification.AllGood S mid := by
      have hh := (Verification.wordGood_reach S hs hmreach).mp
        ((Verification.wordGood_ofFn S f).mpr hg)
      exact (Verification.wordGood_ofFn S mid).mp hh
    exact (ih (g:=mid) hm).trans (decoded_step hd (layout_reach hl hmreach)
      (reach_syntax hmreach hs) hmgood hmstep)

lemma encoded_idle (u : Fin n → Fin d → ZMod 2) (i : Fin (n*width q)) :
    (encoded u i).marker=.idle := rfl

theorem clean_decoded_reach {S : Schedule q} (hd : d≤q) (u : Fin n → Fin d → ZMod 2)
    (g : Fin (n*width q) → Cell q)
    (hr : Reach S d (encodeWord (List.ofFn u)) (List.ofFn g)) :
    CheckedReach S hd (List.ofFn u) (List.ofFn (decoded hd g)) := by
  have hf : Syntax S d (List.ofFn (encoded (q:=q) u)) := by
    rw [encoded_ofFn]
    exact encodeWord_syntax _
  have hg : Verification.AllGood S (encoded (q:=q) u) :=
    Verification.allGood_of_idle S (encoded u) (encoded_idle u)
  rw [←encoded_ofFn] at hr
  simpa [decoded_encoded] using decoded_reach hd (layout_encoded u) hf hg hr

lemma component_context {S : Schedule q} {f : Fin (n*width q) → Cell q}
    (hd : d≤q) (hl : Layout f) (hs : Syntax S d (List.ofFn f))
    (i : Fin (n*width q)) (hi : (f i).marker=.full) :
    ∃ p t : List (Fin d → ZMod 2),
      List.ofFn (decoded hd f)=p++(Component.region f i hs hi).dataWord hd (f i).head.side++t := by
  let R := Component.region f i hs hi
  have hv (b : Fin ((f i).metadata.arity.val+1)) (p : Fin d) :
      decoded hd f (regionBlock hl hs i hi b) p=R.slot (f i).head.side b (p.castLE hd) := by
    rw [decoded,Committed.owned (Verification.coherent_of_syntax S hs)
      ⟨(regionCore_owned hl hs i hi b (p.castLE hd)).symm,Or.inr hi⟩]
    change _ = (R.cell (R.locate b (p.castLE hd))).data _
    rw [region_cell hl hs i hi]
  have hb : (block (Component.left f i)).val+((f i).metadata.arity.val+1)≤n := by
    have hh := component_last_block hl hs i hi
    have hr := (block (Component.right f i)).isLt
    omega
  obtain ⟨p,t,hf,_⟩ := context_of_interval (decoded hd f) (decoded hd f)
    (block (Component.left f i)).val ((f i).metadata.arity.val+1) hb
    (fun b p => R.slot (f i).head.side b (p.castLE hd))
    (fun b p => R.slot (f i).head.side b (p.castLE hd))
    (fun b => funext (hv b)) (fun b => funext (hv b)) (fun _ _ => rfl)
  exact ⟨p,t,hf⟩

theorem semanticZero_checked {S : Schedule q} {f : Fin (n*width q) → Cell q}
    (hd : d≤q) (hl : Layout f) (hs : Syntax S d (List.ofFn f))
    (hg : Verification.AllGood S f) (i : Fin (n*width q)) (hz : SemanticZero S (f i)) :
    CheckedZero S hd (List.ofFn (decoded hd f)) := by
  have hi : (f i).marker=.full := hz.1
  have hh := Verification.good_semanticZero_sound S (hg i hi) hz
  have hfmt := hs.2.2 (f i) (List.mem_ofFn.mpr ⟨i,rfl⟩)
  have hs0 : (f i).head.side=false := hfmt.2.2.2.2.2.2.2.1 (Or.inr hi) hh.2.1
  obtain ⟨p,t,hp⟩ := component_context hd hl hs i hi
  refine ⟨Component.region f i hs hi,p,t,hh.2.1,
    Component.region_holds f i hs hi (hg i hi) hh.1,?_⟩
  simpa [hs0] using hp

end Rigid
end

section
open LocalSyntax LocalSyntax.Skeleton
variable {q d : ℕ} [NeZero q]
namespace Cell
def CheckerSafe (c : Cell q) : Prop := ∀x, c.pos=.palette x → c.checker≠.passed x
omit [NeZero q] in
lemma checkerSafe_idle (c : Cell q) (hc : c.checker=.idle) : c.CheckerSafe := by
  intro x hx
  simp [hc]
end Cell

lemma unary_checkerSafe {S : Schedule q} {a b : Cell q} (hu : Unary S a b) :
    a.CheckerSafe ↔ b.CheckerSafe := by cases hu <;> exact Iff.rfl

lemma binary_checkerSafe {S : Schedule q} {a b a' b' : Cell q} (hu : Binary S a b a' b') :
    (a.CheckerSafe ∧ b.CheckerSafe) ↔ (a'.CheckerSafe ∧ b'.CheckerSafe) := by
  cases hu with
  | acquire => exact Iff.rfl
  | read_left => exact Iff.rfl
  | read_right => exact Iff.rfl
  | undo_left => exact Iff.rfl
  | undo_right => exact Iff.rfl
  | checker_create a b p x ha hp hb =>
    simp [Cell.CheckerSafe,Cell.setChecker]
  | checker_advance a b v x ha hb hv =>
    change a.skeleton.pos=.palette v at ha
    simp [Cell.CheckerSafe,Cell.setChecker,Cell.pos,ha,Ne.symm hv]
  | swap => exact and_comm

lemma checkerSafe_step {S : Schedule q} {v w : List (Cell q)} (he : Step S d v w) :
    (∀c∈v,c.CheckerSafe) ↔ (∀c∈w,c.CheckerSafe) := by
  obtain ⟨p,s,a,b,rfl,rfl,hh⟩ := he
  have hs : (∀c∈a,c.CheckerSafe) ↔ (∀c∈b,c.CheckerSafe) := by
    rcases hh.2 with ⟨a,b,rfl,rfl,h⟩|⟨a,b,a',b',rfl,rfl,h⟩
    · simpa using h.elim unary_checkerSafe (fun h => (unary_checkerSafe h).symm)
    · simpa using h.elim binary_checkerSafe (fun h => (binary_checkerSafe h).symm)
  simpa only [List.forall_mem_append] using (and_congr (and_congr Iff.rfl hs) Iff.rfl)

lemma checkerSafe_reach {S : Schedule q} {v w : List (Cell q)} (he : Reach S d v w) :
    (∀c∈v,c.CheckerSafe) ↔ (∀c∈w,c.CheckerSafe) := by
  induction he with
  | refl => rfl
  | tail h e ih => exact ih.trans (checkerSafe_step e)

lemma encodeWord_checkerSafe (u : List (Fin d → ZMod 2)) :
    ∀c∈encodeWord (q:=q) u,c.CheckerSafe := by
  intro c hc
  obtain ⟨bits,hb,hc⟩ := List.mem_flatMap.mp hc
  apply Cell.checkerSafe_idle
  simp only [canonicalBlock,List.mem_append,List.mem_map,List.mem_singleton] at hc
  rcases hc with (⟨p,_,rfl⟩|⟨p,_,rfl⟩)|rfl <;> rfl

end

section
open LocalSyntax LocalSyntax.Skeleton
variable {q d n : ℕ} [NeZero q]
namespace Cell
lemma color_eq (a : Cell q) (x : Fin q) (h : a.pos=.palette x) : a.color=x := by
  simp [color,h]
end Cell
namespace Rigid

def palCell (b : Fin n) (p : Fin q) : Fin (n*width q) := cell b ⟨q+p.val,by
  have := p.isLt; dsimp [width]; omega⟩

def colors (f : Fin (n*width q) → Cell q) (b : Fin n) : List (Fin q) :=
  List.ofFn (fun p => (f (palCell b p)).color)

lemma position_palette_iff (i : Fin (width q)) :
    (∃x, position i=.palette x) ↔ q ≤ i.val ∧ i.val < 2*q := by
  unfold position
  split_ifs <;> simp_all; omega

lemma layout_palette_iff {f : Fin (n*width q) → Cell q} (hl : Layout f)
    (i : Fin (n*width q)) : (f i).isPalette ↔ q ≤ i.val%width q ∧ i.val%width q < 2*q := by
  have hshape : (f i).isPalette ↔ (f i).shape=.palette := by
    cases he : (f i).pos <;> simp [Cell.shape,Cell.isPalette,he]
  rw [hshape,hl]
  have he : shape (coord i)=.palette ↔ ∃x,position (coord i)=.palette x := by
    cases he : position (coord i) <;> simp [shape,he]
  rw [he,position_palette_iff]
  rfl

omit [NeZero q] in
lemma palCell_injective (b : Fin n) : Function.Injective (palCell (q:=q) b) := by
  intro x y h
  apply Fin.ext
  have hh := congrArg Fin.val h
  change b.val*width q+(q+x.val)=b.val*width q+(q+y.val) at hh
  omega

lemma palCell_palette {f : Fin (n*width q) → Cell q} (hl : Layout f) (b : Fin n) (p : Fin q) :
    (f (palCell b p)).isPalette := by
  rw [layout_palette_iff hl]
  have hh := congrArg Fin.val (coord_cell b (⟨q+p.val,by have := p.isLt; dsimp [width]; omega⟩ : Fin (width q)))
  change (palCell b p).val%width q=q+p.val at hh
  rw [hh]
  have := p.isLt
  omega

noncomputable def palOffset {f : Fin (n*width q) → Cell q} (hl : Layout f)
    (i : Fin (n*width q)) (hi : (f i).isPalette) : Fin q :=
  ⟨i.val%width q-q,by have := (layout_palette_iff hl i).mp hi; omega⟩

lemma palOffset_cell {f : Fin (n*width q) → Cell q} (hl : Layout f)
    (i : Fin (n*width q)) (hi : (f i).isPalette) :
    palCell (block i) (palOffset hl i hi)=i := by
  have hh := (layout_palette_iff hl i).mp hi
  have he := cell_block_coord i
  apply Fin.ext
  have he' := congrArg Fin.val he
  change (block i).val*width q+(q+(i.val%width q-q))=i.val
  change (block i).val*width q+(i.val%width q)=i.val at he'
  omega

lemma adjacent_palettes_block {f : Fin (n*width q) → Cell q} (hl : Layout f)
    (i j : Fin (n*width q)) (hij : i.val+1=j.val) (hi : (f i).isPalette) :
    block i=block j := by
  have hh := (layout_palette_iff hl i).mp hi
  have hb := block_next hij
  rw [ite_eq_right (by omega),Nat.add_zero] at hb
  exact Fin.ext hb.symm

lemma colors_pos {f g : Fin (n*width q) → Cell q} (h : ∀i,(f i).pos=(g i).pos) (b : Fin n) :
    colors f b=colors g b := by
  apply congrArg List.ofFn
  funext p
  simp only [Cell.color,h]

lemma colors_swap {f g : Fin (n*width q) → Cell q} (hl : Layout f)
    (i j : Fin (n*width q)) (hij : i.val+1=j.val) (hi : (f i).isPalette) (hj : (f j).isPalette)
    (hgi : g i=f j) (hgj : g j=f i) (ho : ∀k,k≠i → k≠j → f k=g k) (b : Fin n) :
    (colors f b).Perm (colors g b) := by
  classical
  have hb := adjacent_palettes_block hl i j hij hi
  by_cases hbi : block i=b
  · let pi := palOffset hl i hi
    let pj := palOffset hl j hj
    have hei : palCell b pi=i := by rw [←hbi]; exact palOffset_cell hl i hi
    have hej : palCell b pj=j := by rw [←hbi,hb]; exact palOffset_cell hl j hj
    have he : (fun p => (g (palCell b p)).color)=
        (fun p => (f (palCell b p)).color) ∘ Equiv.swap pi pj := by
      funext p
      by_cases hp : p=pi
      · subst p
        simp [hei,hej,hgi]
      · by_cases hp' : p=pj
        · subst p
          simp [hei,hej,hgj]
        · rw [Function.comp_apply,Equiv.swap_apply_of_ne_of_ne hp hp']
          rw [←ho]
          · intro h
            exact hp (palCell_injective b (h.trans hei.symm))
          · intro h
            exact hp' (palCell_injective b (h.trans hej.symm))
    unfold colors
    rw [he]
    exact ((Equiv.swap pi pj).ofFn_comp_perm _).symm
  · have hbj : block j≠b := by rwa [←hb]
    have he : colors f b=colors g b := by
      apply congrArg List.ofFn
      funext p
      rw [ho]
      · intro h
        have hh := congrArg block h
        rw [palCell,block_cell] at hh
        exact hbi hh.symm
      · intro h
        have hh := congrArg block h
        rw [palCell,block_cell] at hh
        exact hbj hh.symm
    rw [he]

lemma unary_colors {S : Schedule q} {f g : Fin (n*width q) → Cell q}
    {i : Fin (n*width q)} (hu : UnaryAt S f g i) (b : Fin n) :
    colors f b=colors g b := by
  apply colors_pos
  intro k
  by_cases hk : k=i
  · subst k
    have hh {a c : Cell q} (he : Unary S a c) : a.pos=c.pos := by cases he <;> rfl
    exact hh hu.edge
  · rw [hu.off k hk]

lemma binary_colors {S : Schedule q} {f g : Fin (n*width q) → Cell q}
    (hl : Layout f) {i j : Fin (n*width q)} (hu : BinaryAt S f g i j) (b : Fin n) :
    (colors f b).Perm (colors g b) := by
  have hh := hu.edge
  generalize hfi : f i=a at hh
  generalize hfj : f j=c at hh
  generalize hgi : g i=a' at hh
  generalize hgj : g j=c' at hh
  cases hh with
  | swap a c x y ha hc he hn hn' =>
    exact colors_swap hl i j hu.adjacent ⟨x,(congrArg Cell.pos hfi).trans ha⟩ ⟨y,(congrArg Cell.pos hfj).trans hc⟩
      (hgi.trans hfj.symm) (hgj.trans hfi.symm) hu.off b
  | _ =>
    apply List.Perm.of_eq
    apply colors_pos
    intro k
    by_cases hk : k=i
    · subst k; rw [hfi,hgi] <;> rfl
    · by_cases hk' : k=j
      · subst k; rw [hfj,hgj]; rfl
      · rw [hu.off k hk hk']

lemma colors_step {S : Schedule q} {f g : Fin (n*width q) → Cell q}
    (hl : Layout f) (he : Step S d (List.ofFn f) (List.ofFn g)) (b : Fin n) :
    (colors f b).Perm (colors g b) := by
  have hlg := layout_reach hl (Relation.ReflTransGen.single he)
  obtain ⟨p,s,v,w,hf,hg,hr⟩ := he
  rcases hr.2 with ⟨a,c,rfl,rfl,hh⟩|⟨a,c,a',c',rfl,rfl,hh⟩
  · rcases hh with hh|hh
    · obtain ⟨i,hi⟩ := Committed.unaryAt_context hf hg hh
      exact List.Perm.of_eq (unary_colors hi b)
    · obtain ⟨i,hi⟩ := Committed.unaryAt_context hg hf hh
      exact (List.Perm.of_eq (unary_colors hi b)).symm
  · rcases hh with hh|hh
    · obtain ⟨i,j,hij⟩ := Committed.binaryAt_context hf hg hh
      exact binary_colors hl hij b
    · obtain ⟨i,j,hij⟩ := Committed.binaryAt_context hg hf hh
      exact (binary_colors hlg hij b).symm

lemma colors_reach {S : Schedule q} {f g : Fin (n*width q) → Cell q}
    (hl : Layout f) (hr : Reach S d (List.ofFn f) (List.ofFn g)) (b : Fin n) :
    (colors f b).Perm (colors g b) := by
  generalize he : List.ofFn g=w at hr
  induction hr generalizing g with
  | refl =>
    have hfg : f=g := List.ofFn_injective he.symm
    subst g
    exact .refl _
  | @tail v w h e ih =>
    have hvlen : v.length=n*width q := by have hh := reach_length h; simpa using hh.symm
    let mid : Fin (n*width q) → Cell q := fun i => v.get (Fin.cast hvlen.symm i)
    have hm : List.ofFn mid=v := by
      rw [show mid=(fun i => v.get (Fin.cast hvlen.symm i)) from rfl,
        ←List.ofFn_congr hvlen v.get]
      exact List.ofFn_get v
    have hmreach : Reach S d (List.ofFn f) (List.ofFn mid) := by rwa [hm]
    have hmstep : Step S d (List.ofFn mid) (List.ofFn g) := by rwa [hm,he]
    exact (ih (g:=mid) hm).trans (colors_step (layout_reach hl hmreach) hmstep b)

omit [NeZero q] in
lemma pal_position (p : Fin q) : position (⟨q+p.val,by have := p.isLt; dsimp [width]; omega⟩ : Fin (width q))=.palette p := by
  have := p.isLt
  simp [position,show ¬q+p.val<q by omega,show q+p.val<2*q by omega]

lemma encoded_colors (u : Fin n → Fin d → ZMod 2) (b : Fin n) :
    colors (encoded (q:=q) u) b=List.finRange q := by
  rw [←List.ofFn_id]
  apply congrArg List.ofFn
  funext p
  rw [palCell,encoded_cell,pal_position]
  rfl

lemma clean_colors {S : Schedule q} (u : Fin n → Fin d → ZMod 2) (g : Fin (n*width q) → Cell q)
    (hr : Reach S d (encodeWord (List.ofFn u)) (List.ofFn g)) (b : Fin n) :
    (colors g b).Nodup ∧ ∀x,x∈colors g b := by
  rw [←encoded_ofFn] at hr
  have hh := colors_reach (layout_encoded u) hr b
  rw [encoded_colors] at hh
  exact ⟨hh.nodup_iff.mp (List.nodup_finRange q),fun x => hh.mem_iff.mp (List.mem_finRange x)⟩

lemma checker_adjacent {S : Schedule q} {f : Fin (n*width q) → Cell q}
    (hs : Syntax S d (List.ofFn f)) (i j : Fin (n*width q)) (hij : i.val+1=j.val) :
    CheckerPair (f i) (f j) := by
  have hh := List.isChain_ofFn.mp hs.2.1 i.val (by rw [hij]; exact j.isLt)
  convert hh using 1
  congr 1
  exact Fin.ext hij.symm

def viewCell (f : Fin (n*width q) → Cell q) (b : Fin n) (p : Fin q) : Palette.Cell (Fin q) Unit :=
  ⟨(f (palCell b p)).color,(f (palCell b p)).checker,()⟩

def paletteView (f : Fin (n*width q) → Cell q) (b : Fin n) := List.ofFn (viewCell f b)

lemma paletteView_syntax {S : Schedule q} {f : Fin (n*width q) → Cell q}
    (hl : Layout f) (hs : Syntax S d (List.ofFn f)) (b : Fin n) :
    Palette.Syntax (paletteView f b) := by
  constructor
  · apply List.isChain_ofFn.mpr
    intro p hp
    have hh := checker_adjacent hs (palCell b ⟨p,by omega⟩) (palCell b ⟨p+1,hp⟩) (by simp [palCell,cell,Nat.add_assoc])
    exact hh.1 ⟨palCell_palette hl _ _,palCell_palette hl _ _⟩
  · intro c hc
    have he : paletteView f b≠[] := by simp [paletteView,NeZero.ne q]
    rw [List.getLast?_eq_some_getLast he] at hc
    simp only [paletteView,List.getLast_ofFn,Option.mem_def,Option.some.injEq] at hc
    subst c
    let p : Fin q := ⟨q-1,by have := NeZero.pos q; omega⟩
    let z : Fin (n*width q) := cell b ⟨2*q,by simp [width]⟩
    have hpos : (f z).pos=.stop := by rw [layout_stop_iff hl]; exact congrArg Fin.val (coord_cell _ _)
    have hh := checker_adjacent hs (palCell b p) z (by
      have := NeZero.pos q
      dsimp [palCell,cell,z,p]
      omega)
    exact hh.2 ⟨palCell_palette hl _ _,hpos⟩

lemma palette_equal_colors_absurd {f : Fin (n*width q) → Cell q} (hl : Layout f)
    (hn : ∀b,(colors f b).Nodup) (i j : Fin (n*width q)) (hij : i.val+1=j.val)
    (x : Fin q) (hi : (f i).pos=.palette x) (hj : (f j).pos=.palette x) : False := by
  have hb := adjacent_palettes_block hl i j hij ⟨x,hi⟩
  let pi := palOffset hl i ⟨x,hi⟩
  let pj := palOffset hl j ⟨x,hj⟩
  have hei : palCell (block i) pi=i := palOffset_cell hl i ⟨x,hi⟩
  have hej : palCell (block i) pj=j := by rw [hb]; exact palOffset_cell hl j ⟨x,hj⟩
  have hc : (f (palCell (block i) pi)).color=(f (palCell (block i) pj)).color := by
    rw [hei,hej,Cell.color_eq _ _ hi,Cell.color_eq _ _ hj]
  have he := List.nodup_ofFn.mp (hn (block i)) hc
  have hh : i=j := hei.symm.trans ((congrArg (palCell (block i)) he).trans hej)
  have hv := congrArg Fin.val hh
  omega

end Rigid
end

open LocalSyntax LocalSyntax.Skeleton
namespace Rigid
variable {q d n : ℕ} [NeZero q]

lemma paletteView_safe {f : Fin (n*width q) → Cell q} (hl : Layout f)
    (hsafe : ∀i,(f i).CheckerSafe) (b : Fin n) : Palette.Safe (paletteView f b) := by
  rintro c hc x hcheck hcolor
  obtain ⟨p,rfl⟩ := List.mem_ofFn.mp hc
  obtain ⟨v,hpos⟩ := palCell_palette hl b p
  have hsv := hsafe (palCell b p)
  have hpx : (f (palCell b p)).pos=.palette x := by
    rw [hpos]
    apply congrArg Position.palette
    exact (Cell.color_eq _ _ hpos).symm.trans hcolor
  exact hsv x hpx hcheck

lemma paletteView_nonzero {S : Schedule q} {f : Fin (n*width q) → Cell q}
    (hl : Layout f) (hs : Syntax S d (List.ofFn f)) (hsafe : ∀i,(f i).CheckerSafe)
    (hcolors : ∀b,(colors f b).Nodup ∧ ∀x,x∈colors f b) (b : Fin n) :
    ¬Palette.Zero (paletteView f b) := by
  apply Palette.not_zero_of_invariants (paletteView_syntax hl hs b) (paletteView_safe hl hsafe b)
  · simpa [paletteView,List.map_ofFn,viewCell,colors,Function.comp_def] using (hcolors b).1
  · simpa [paletteView,List.map_ofFn,viewCell,colors,Function.comp_def] using (hcolors b).2

lemma palette_stop_last {f : Fin (n*width q) → Cell q} (hl : Layout f)
    (i j : Fin (n*width q)) (hij : i.val+1=j.val) (hi : (f i).isPalette)
    (hj : (f j).pos=.stop) :
    i=palCell (block i) ⟨q-1,by have := NeZero.pos q; omega⟩ := by
  have hr := (layout_palette_iff hl i).mp hi
  have hjr := (layout_stop_iff hl j).mp hj
  have h1 : 1<width q := by have := NeZero.pos q; dsimp [width]; omega
  have hb : i.val%width q+1<width q := by change i.val%width q+1<2*q+1; omega
  rw [←hij,Nat.add_mod,Nat.mod_eq_of_lt h1,Nat.mod_eq_of_lt hb] at hjr
  have he := palOffset_cell hl i hi
  calc
    i = palCell (block i) (palOffset hl i hi) := he.symm
    _ = palCell (block i) ⟨q-1,by have := NeZero.pos q; omega⟩ := by
      apply congrArg (palCell (block i))
      apply Fin.ext
      change i.val%width q-q=q-1
      omega

lemma no_failed_checker {S : Schedule q} {f : Fin (n*width q) → Cell q}
    (hl : Layout f) (hs : Syntax S d (List.ofFn f)) (hsafe : ∀i,(f i).CheckerSafe)
    (hcolors : ∀b,(colors f b).Nodup ∧ ∀x,x∈colors f b)
    (i j : Fin (n*width q)) (hij : i.val+1=j.val)
    (x y : Fin q) (hix : (f i).pos=.palette x) (hiy : (f i).checker=.head y)
    (hj : (f j).pos=.stop) (hxy : x≠y) : False := by
  let b := block i
  let p : Fin q := ⟨q-1,by have := NeZero.pos q; omega⟩
  have hei : palCell b p=i := (palette_stop_last hl i j hij ⟨x,hix⟩ hj).symm
  apply paletteView_nonzero hl hs hsafe hcolors b
  right; right
  refine ⟨(paletteView f b).take (q-1),viewCell f b p,y,?_,?_,?_⟩
  · have hh := ofFn_split_one (viewCell f b) p
    have hp : p.val+1=q := by have := NeZero.pos q; dsimp [p]; omega
    rw [hp,List.drop_eq_nil_of_le (by simp)] at hh
    simpa [paletteView,p] using hh
  · change (f (palCell b p)).checker=.head y
    rwa [hei]
  · change (f (palCell b p)).color≠y
    rwa [hei,Cell.color_eq _ _ hix]

lemma no_binaryZero {S : Schedule q} {f : Fin (n*width q) → Cell q}
    (hl : Layout f) (hs : Syntax S d (List.ofFn f)) (hsafe : ∀i,(f i).CheckerSafe)
    (hcolors : ∀b,(colors f b).Nodup ∧ ∀x,x∈colors f b)
    (i j : Fin (n*width q)) (hij : i.val+1=j.val) : ¬BinaryZero (f i) (f j) := by
  rintro (hp|⟨x,hi,hj⟩|⟨x,y,hi,hhead,hstop,hxy⟩)
  · exact hp ⟨Verification.coherent_of_syntax S hs i j hij,checker_adjacent hs i j hij⟩
  · exact palette_equal_colors_absurd hl (fun b => (hcolors b).1) i j hij x hi hj
  · exact no_failed_checker hl hs hsafe hcolors i j hij x y hi hhead hstop hxy

lemma unaryZero_semantic {S : Schedule q} {f : Fin (n*width q) → Cell q}
    (hs : Syntax S d (List.ofFn f)) (hsafe : ∀i,(f i).CheckerSafe)
    (i : Fin (n*width q)) (hz : UnaryZero S d (f i)) : SemanticZero S (f i) := by
  rcases hz with hf|hz|⟨x,hp,hc⟩
  · exact (hf (hs.2.2 (f i) (List.mem_ofFn.mpr ⟨i,rfl⟩))).elim
  · exact hz
  · exact (hsafe i x hp hc).elim

theorem contextualZero_checked {S : Schedule q} {f : Fin (n*width q) → Cell q}
    (hd : d≤q) (hl : Layout f) (hs : Syntax S d (List.ofFn f))
    (hg : Verification.AllGood S f) (hsafe : ∀i,(f i).CheckerSafe)
    (hcolors : ∀b,(colors f b).Nodup ∧ ∀x,x∈colors f b)
    (p z t : List (Cell q)) (hw : List.ofFn f=p++z++t) (hz : Zero S d z) :
    CheckedZero S hd (List.ofFn (decoded hd f)) := by
  rcases hz with ⟨a,rfl,ha⟩|⟨a,b,rfl,hab⟩
  · have hn := congrArg List.length hw
    simp only [List.length_ofFn,List.length_append,List.length_singleton] at hn
    let i : Fin (n*width q) := ⟨p.length,by omega⟩
    have hi : f i=a := by simpa using Verification.get_of_context hw i 0 (by simp) (by simp [i])
    exact semanticZero_checked hd hl hs hg i (unaryZero_semantic hs hsafe i (hi ▸ ha))
  · have hn := congrArg List.length hw
    simp only [List.length_ofFn,List.length_append,List.length_cons,List.length_nil] at hn
    let i : Fin (n*width q) := ⟨p.length,by omega⟩
    let j : Fin (n*width q) := ⟨p.length+1,by omega⟩
    have hi : f i=a := by simpa using Verification.get_of_context hw i 0 (by simp) (by simp [i])
    have hj : f j=b := by simpa using Verification.get_of_context hw j 1 (by simp) (by simp [j])
    exact ((no_binaryZero hl hs hsafe hcolors i j rfl) (by rwa [hi,hj])).elim

theorem clean_zero_decodes {S : Schedule q} (hd : d≤q)
    (u : Fin n → Fin d → ZMod 2) (p z t : List (Cell q))
    (hr : Reach S d (encodeWord (List.ofFn u)) (p++z++t)) (hz : Zero S d z) :
    ∃ v, CheckedReach S hd (List.ofFn u) v ∧ CheckedZero S hd v := by
  let w := p++z++t
  have hn : w.length=n*width q := by
    have hh := reach_length hr
    simpa [w,encodeWord_length,width,Nat.mul_comm] using hh.symm
  let g : Fin (n*width q) → Cell q := fun i => w.get (Fin.cast hn.symm i)
  have hg : List.ofFn g=w := by
    rw [show g=(fun i => w.get (Fin.cast hn.symm i)) from rfl,
      ←List.ofFn_congr hn w.get]
    exact List.ofFn_get w
  have hr' : Reach S d (encodeWord (List.ofFn u)) (List.ofFn g) := by rwa [hg]
  have hs : Syntax S d (List.ofFn g) := reach_syntax hr' (encodeWord_syntax _)
  have he : Reach S d (List.ofFn (encoded (q:=q) u)) (List.ofFn g) := by
    rwa [encoded_ofFn]
  have hl := layout_reach (layout_encoded u) he
  have hv : Verification.AllGood S g :=
    (Verification.wordGood_ofFn S g).mp ((Verification.wordGood_reach S
      (by rw [encoded_ofFn]; exact encodeWord_syntax _) he).mp
      ((Verification.wordGood_ofFn S (encoded (q:=q) u)).mpr
        (Verification.allGood_of_idle S (encoded u) (encoded_idle u))))
  have hsafe : ∀i,(g i).CheckerSafe := by
    intro i
    exact (checkerSafe_reach hr').mp (encodeWord_checkerSafe _) _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  exact ⟨List.ofFn (decoded hd g),clean_decoded_reach hd u g hr',
    contextualZero_checked hd hl hs hv hsafe (clean_colors u g hr') p z t hg hz⟩

theorem clean_survives {S : Schedule q} (hd : d≤q) (u : List (Fin d → ZMod 2))
    (hu : ∀v, CheckedReach S hd u v → ¬CheckedZero S hd v) :
    Survives S d (encodeWord u) := by
  intro p z t hr hz
  have hr' : Reach S d (encodeWord (List.ofFn u.get)) (p++z++t) := by simpa using hr
  obtain ⟨v,hv,hzv⟩ := clean_zero_decodes hd u.get p z t hr' hz
  exact hu v (by simpa using hv) hzv

end Rigid
end SourceBurnside.FiniteTable

end OAI
