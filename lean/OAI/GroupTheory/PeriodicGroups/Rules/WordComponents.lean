import Mathlib
import OAI.GroupTheory.PeriodicGroups.Rules.CommittedWords

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q N : ℕ} [NeZero q]

inductive Shape (q : ℕ)
  | core (p : Fin q) | palette | stop
  deriving DecidableEq

def Cell.shape (c : Cell q) : Shape q := match c.pos with
  | .core p => .core p | .palette _ => .palette | .stop => .stop

lemma Unary.shape {S : Schedule q} {a b : Cell q} (hu : Unary S a b) :
    a.shape=b.shape := by
  cases hu <;> rfl

lemma Binary.shape {S : Schedule q} {a b a' b' : Cell q} (hb : Binary S a b a' b') :
    a.shape=a'.shape ∧ b.shape=b'.shape := by
  cases hb with
  | acquire a b s hp => exact ⟨rfl,rfl⟩
  | read_left a b s j r hp => exact ⟨rfl,rfl⟩
  | read_right a b s j r hp => exact ⟨rfl,rfl⟩
  | undo_left a b s j r hp => exact ⟨rfl,rfl⟩
  | undo_right a b s j r hp => exact ⟨rfl,rfl⟩
  | checker_create a b p x ha hp hb => exact ⟨rfl,rfl⟩
  | checker_advance a b v x ha hb hv => exact ⟨rfl,rfl⟩
  | swap a b x y ha hb he hf hf' => simp [Cell.shape,ha,hb]

lemma replacement_shape {S : Schedule q} {d : ℕ} {v w : List (Cell q)}
    (hr : Replacement S d v w) : v.map Cell.shape=w.map Cell.shape := by
  rcases hr.2 with ⟨a,b,rfl,rfl,h⟩ | ⟨a,b,a',b',rfl,rfl,h⟩
  · rcases h with h | h
    · simpa using h.shape
    · simpa using h.shape.symm
  · rcases h with h | h
    · simp only [List.map_cons,List.map_nil,h.shape.1,h.shape.2]
    · simp only [List.map_cons,List.map_nil,←h.shape.1,←h.shape.2]

lemma step_shape {S : Schedule q} {d : ℕ} {v w : List (Cell q)}
    (hr : Step S d v w) : v.map Cell.shape=w.map Cell.shape := by
  obtain ⟨p,s,v,w,rfl,rfl,hr⟩ := hr
  simp only [List.map_append,replacement_shape hr]

lemma reach_shape {S : Schedule q} {d : ℕ} {v w : List (Cell q)}
    (hr : Reach S d v w) : v.map Cell.shape=w.map Cell.shape := by
  induction hr with
  | refl => rfl
  | tail hr he ih => exact ih.trans (step_shape he)

def Exterior (f : Fin N → Cell q) : Prop :=
  (∀ i, i.val=0 → (f i).skeleton.leftExternal) ∧
  (∀ i, i.val+1=N → (f i).skeleton.rightExternal)

lemma exterior_of_syntax {S : Schedule q} {d : ℕ} {f : Fin N → Cell q}
    (hf : Syntax S d (List.ofFn f)) : Exterior f := by
  have hh : Skeleton.Closed (List.ofFn (fun i => (f i).skeleton)) := by
    simpa only [List.map_ofFn,Function.comp_def] using hf.1
  constructor
  · intro i hi
    apply Skeleton.closed_left hh
    rw [List.head?_eq_getElem?,List.getElem?_eq_getElem (by simp only [List.length_ofFn]; have := i.isLt; omega)]
    simp only [List.getElem_ofFn,Option.mem_def,Option.some.injEq]
    apply congrArg (fun j => (f j).skeleton)
    exact Fin.ext hi.symm
  · intro i hi
    apply Skeleton.closed_right hh
    rw [List.getLast?_eq_getElem?]
    simp only [List.length_ofFn]
    rw [List.getElem?_eq_getElem (by simp only [List.length_ofFn]; have := i.isLt; omega)]
    simp only [List.getElem_ofFn,Option.mem_def,Option.some.injEq]
    apply congrArg (fun j => (f j).skeleton)
    exact Fin.ext (by dsimp; omega)

omit [NeZero q] in
lemma Coherent.owner_right {f : Fin N → Cell q} (hf : Coherent f)
    (he : Exterior f) (i : Fin N) (hi : (f i).marker=.left) :
    ∃ h, i.val < h.val ∧ Own f i h := by
  change (f i).skeleton.marker=.left at hi
  generalize hdiff : N-i.val=n
  induction n using Nat.strong_induction_on generalizing i with
  | h n ih =>
    have hn : i.val+1 < N := by
      by_contra h
      have hx := he.2 i (by have := i.isLt; omega)
      simp [Skeleton.rightExternal,hi] at hx
    let j : Fin N := ⟨i.val+1,hn⟩
    have hij : i.val+1=j.val := rfl
    have hcut : ¬cellCut f i := by
      simp [cellCut,Skeleton.rightExternal,hi]
    have hc : SameRegion f i j := (Connected.adjacent_iff hij).mpr hcut
    have hm := Skeleton.internal_marker_rule (hf.internal i j hij hc)
    have hj : (f j).marker=.left ∨ (f j).marker=.boundary ∨ (f j).marker=.full := by
      simpa [Cell.marker,hi] using hm
    rcases hj with hj | hj | hj
    · obtain ⟨h,hh,ho⟩ := ih (N-j.val) (by dsimp [j]; omega) j hj rfl
      exact ⟨h,by dsimp [j] at hh; omega,hc.trans ho.1,ho.2⟩
    · exact ⟨j,by dsimp [j]; omega,hc,Or.inl hj⟩
    · exact ⟨j,by dsimp [j]; omega,hc,Or.inr hj⟩

omit [NeZero q] in
lemma Coherent.owner_left {f : Fin N → Cell q} (hf : Coherent f)
    (he : Exterior f) (i : Fin N) (hi : (f i).marker=.right) :
    ∃ h, h.val < i.val ∧ Own f i h := by
  change (f i).skeleton.marker=.right at hi
  generalize hdiff : i.val=n
  induction n using Nat.strong_induction_on generalizing i with
  | h n ih =>
    have hn : 0 < i.val := by
      by_contra h
      have hx := he.1 i (by omega)
      simp [Skeleton.leftExternal,hi] at hx
    let j : Fin N := ⟨i.val-1,by have := i.isLt; omega⟩
    have hij : j.val+1=i.val := by dsimp [j]; omega
    have hp := hf j i hij
    have hcut : ¬cellCut f j := by
      rcases hp.2 with hp | hp
      · simp [Skeleton.leftExternal,hi] at hp
      · exact hp.1
    have hc : SameRegion f j i := (Connected.adjacent_iff hij).mpr hcut
    have hm := (hf.internal j i hij hc).1.2
    have hj : (f j).marker=.full ∨ (f j).marker=.right := by
      rcases hm with hm | hm
      · exact (hcut hm.1).elim
      · simpa [Skeleton.acceptsLeft,Cell.marker,hi] using hm.2.2.2.1
    rcases hj with hj | hj
    · exact ⟨j,by dsimp [j]; omega,hc.symm,Or.inr hj⟩
    · obtain ⟨h,hh,ho⟩ := ih j.val (by dsimp [j]; omega) j hj rfl
      exact ⟨h,by dsimp [j] at hh; omega,hc.symm.trans ho.1,ho.2⟩

omit [NeZero q] in
theorem Coherent.owner {f : Fin N → Cell q} (hf : Coherent f)
    (he : Exterior f) (i : Fin N) (hi : (f i).marker≠.idle) : ∃ h, Own f i h := by
  cases hm : (f i).marker with
  | idle => exact (hi hm).elim
  | left => obtain ⟨h,_,hh⟩ := hf.owner_right he i hm; exact ⟨h,hh⟩
  | right => obtain ⟨h,_,hh⟩ := hf.owner_left he i hm; exact ⟨h,hh⟩
  | boundary => exact ⟨i,Connected.refl _ _,Or.inl hm⟩
  | full => exact ⟨i,Connected.refl _ _,Or.inr hm⟩

namespace Component
variable (f : Fin N → Cell q) (i : Fin N)
def members : Finset (Fin N) := Finset.univ.filter (SameRegion f i)
omit [NeZero q] in
lemma mem_iff (j : Fin N) : j ∈ members f i ↔ SameRegion f i j := by simp [members]
omit [NeZero q] in
lemma nonempty : (members f i).Nonempty := ⟨i,(mem_iff f i i).mpr (.refl _ _)⟩
noncomputable def left : Fin N := (members f i).min' (nonempty f i)
noncomputable def right : Fin N := (members f i).max' (nonempty f i)
omit [NeZero q] in
lemma connected_left : SameRegion f i (left f i) := by
  exact (mem_iff f i _).mp (Finset.min'_mem _ _)
omit [NeZero q] in
lemma connected_right : SameRegion f i (right f i) := by
  exact (mem_iff f i _).mp (Finset.max'_mem _ _)
omit [NeZero q] in
lemma left_le {j : Fin N} (hj : SameRegion f i j) : left f i ≤ j := by
  exact Finset.min'_le _ _ ((mem_iff f i _).mpr hj)
omit [NeZero q] in
lemma le_right {j : Fin N} (hj : SameRegion f i j) : j ≤ right f i := by
  exact Finset.le_max' _ _ ((mem_iff f i _).mpr hj)
omit [NeZero q] in
lemma left_le_self : left f i ≤ i := left_le f i (.refl _ _)
omit [NeZero q] in
lemma self_le_right : i ≤ right f i := le_right f i (.refl _ _)
omit [NeZero q] in
lemma left_le_right : left f i ≤ right f i := left_le f i (connected_right f i)
omit [NeZero q] in
lemma interval (j : Fin N) : SameRegion f i j ↔ left f i ≤ j ∧ j ≤ right f i := by
  constructor
  · intro h; exact ⟨left_le f i h,le_right f i h⟩
  · rintro ⟨hl,hr⟩
    have h := (connected_left f i).symm.trans (connected_right f i)
    exact h.subinterval (by have := left_le_self f i; have := left_le_right f i; omega)
      (by have := self_le_right f i; have := left_le_right f i; omega)
      (by have := left_le_right f i; omega) (by have := left_le_right f i; omega)

omit [NeZero q] in
lemma exterior_left (hf : Coherent f) (he : Exterior f) : (f (left f i)).skeleton.leftExternal := by
  by_cases hh : (left f i).val=0
  · exact he.1 _ hh
  · let p : Fin N := ⟨(left f i).val-1,by have := (left f i).isLt; omega⟩
    have hp : p.val+1=(left f i).val := by dsimp [p]; omega
    have hc : cellCut f p := by
      by_contra hn
      have hc : SameRegion f i p := (connected_left f i).trans ((Connected.adjacent_iff hp).mpr hn).symm
      have hle := left_le f i hc
      dsimp [p] at hle
      omega
    rcases (hf p (left f i) hp).2 with h | h
    · exact h.2
    · exact (h.1 hc).elim

omit [NeZero q] in
lemma exterior_right (_hf : Coherent f) (he : Exterior f) : cellCut f (right f i) := by
  by_cases hh : (right f i).val+1=N
  · exact he.2 _ hh
  · let p : Fin N := ⟨(right f i).val+1,by have := (right f i).isLt; omega⟩
    have hp : (right f i).val+1=p.val := rfl
    by_contra hn
    have hc : SameRegion f i p := (connected_right f i).trans ((Connected.adjacent_iff hp).mpr hn)
    have hle := le_right f i hc
    dsimp [p] at hle
    omega

omit [NeZero q] in
lemma first (hf : Coherent f) (he : Exterior f) (hi : (f i).skeleton.IsHead) :
    (f (left f i)).skeleton.first := by
  have hn := hf.region_locked hi (connected_left f i).symm
  have hh := exterior_left f i hf he
  rcases hh with hh | hh
  · exact (hn hh).elim
  · exact hh.2

omit [NeZero q] in
lemma last (hf : Coherent f) (he : Exterior f) (hi : (f i).marker=.full) :
    (f (right f i)).skeleton.last := by
  have hih : (f i).skeleton.IsHead := Or.inr hi
  have hn := hf.region_locked hih (connected_right f i).symm
  have hh := exterior_right f i hf he
  rcases hh with hh | hh | hh
  · exact (hn hh).elim
  · have heq := hf.unique_head hih (Or.inl hh) (connected_right f i)
    simp only [←heq] at hh
    change (f i).marker=.boundary at hh
    simp [hi] at hh
  · exact hh.2

noncomputable def size : ℕ := (right f i).val+1-(left f i).val
omit [NeZero q] in
lemma size_pos : 0 < size f i := by
  have := left_le_right f i
  unfold size
  omega
noncomputable def offset (j : Fin (size f i)) : Fin N :=
  ⟨(left f i).val+j.val,by
    have := (right f i).isLt
    have := j.isLt
    have := left_le_right f i
    dsimp [size] at *
    omega⟩
omit [NeZero q] in
lemma connected_offset (j : Fin (size f i)) : SameRegion f i (offset f i j) := by
  apply (interval f i _).mpr
  have := j.isLt
  have := left_le_right f i
  dsimp [size] at *
  constructor
  · change (left f i).val ≤ (left f i).val+j.val; omega
  · change (left f i).val+j.val ≤ (right f i).val; omega
omit [NeZero q] in
lemma offset_adjacent (j k : Fin (size f i)) (hj : j.val+1=k.val) :
    (offset f i j).val+1=(offset f i k).val := by dsimp [offset]; omega
omit [NeZero q] in
lemma offset_internal (hf : Coherent f) (j k : Fin (size f i)) (hj : j.val+1=k.val) :
    Skeleton.Internal (f (offset f i j)).skeleton (f (offset f i k)).skeleton := by
  exact (hf.internal _ _ (offset_adjacent f i j k hj)
    ((connected_offset f i j).symm.trans (connected_offset f i k))).1.2.resolve_left
      (fun h => ((Connected.adjacent_iff (offset_adjacent f i j k hj)).mp
        ((connected_offset f i j).symm.trans (connected_offset f i k))) h.1) |>.2.2.2.2

omit [NeZero q] in
lemma offset_first_iff (hf : Coherent f) (he : Exterior f) (hi : (f i).skeleton.IsHead)
    (j : Fin (size f i)) : (f (offset f i j)).skeleton.first ↔ j.val=0 := by
  constructor
  · intro hj
    by_contra hn
    let k : Fin (size f i) := ⟨j.val-1,by have := j.isLt; omega⟩
    have hk : k.val+1=j.val := by dsimp [k]; omega
    exact (offset_internal f i hf k j hk).2.2.2.1 hj
  · intro hj
    have hh : offset f i j=left f i := Fin.ext (by simp [offset,hj])
    rw [hh]
    exact first f i hf he hi

omit [NeZero q] in
lemma offset_last_iff (hf : Coherent f) (he : Exterior f) (hi : (f i).marker=.full)
    (j : Fin (size f i)) : (f (offset f i j)).skeleton.last ↔ j.val+1=size f i := by
  constructor
  · intro hj
    by_contra hn
    let k : Fin (size f i) := ⟨j.val+1,by have := j.isLt; omega⟩
    have hk : j.val+1=k.val := rfl
    exact (offset_internal f i hf j k hk).2.2.2.2 hj
  · intro hj
    have hh : offset f i j=right f i := Fin.ext (by
      have := left_le_right f i
      dsimp [offset,size] at *
      omega)
    rw [hh]
    exact last f i hf he hi

noncomputable def region {S : Schedule q} {d : ℕ}
    (hs : Syntax S d (List.ofFn f)) (hi : (f i).marker=.full) : Region q d where
  size := size f i
  positive := size_pos f i
  task := (f i).metadata.task
  cell := fun j => f (offset f i j)
  task_eq j := SameRegion.task (Verification.coherent_of_syntax S hs) (connected_offset f i j).symm
  first_iff := offset_first_iff f i (Verification.coherent_of_syntax S hs)
    (exterior_of_syntax hs) (Or.inr hi)
  last_iff := offset_last_iff f i (Verification.coherent_of_syntax S hs) (exterior_of_syntax hs) hi
  adjacent j k hj := ⟨(Verification.coherent_of_syntax S hs _ _ (offset_adjacent f i j k hj)).1,
    offset_internal f i (Verification.coherent_of_syntax S hs) j k hj⟩
  payload_format j := by
    have hh : (f (offset f i j)).Format S d := hs.2.2 _ (List.mem_ofFn.mpr ⟨offset f i j,rfl⟩)
    exact ⟨hh.2.1,hh.2.2.1,hh.2.2.2.1⟩

omit [NeZero q] in
lemma offset_injective : Function.Injective (offset f i) := by
  intro a b hab
  apply Fin.ext
  have hh := congrArg Fin.val hab
  dsimp [offset] at hh
  omega
omit [NeZero q] in
lemma offset_surjective {j : Fin N} (hj : SameRegion f i j) : ∃ k, offset f i k=j := by
  have hh := (interval f i j).mp hj
  let k : Fin (size f i) := ⟨j.val-(left f i).val,by dsimp [size]; omega⟩
  refine ⟨k,Fin.ext ?_⟩
  change (left f i).val+(j.val-(left f i).val)=j.val
  omega

omit [NeZero q] in
lemma sum_offset {A : Type*} [AddCommMonoid A] (a : Fin N → A) :
    (∑ k : Fin (size f i), a (offset f i k)) = ∑ j ∈ members f i, a j := by
  classical
  apply Finset.sum_bij (fun k _ => offset f i k)
  · intro k hk
    exact (mem_iff f i _).mpr (connected_offset f i k)
  · intro a ha b hb hh
    exact offset_injective f i hh
  · intro j hj
    obtain ⟨k,hk⟩ := offset_surjective f i ((mem_iff f i j).mp hj)
    exact ⟨k,Finset.mem_univ _,hk⟩
  · intro k hk; rfl

lemma total_region {S : Schedule q} {d : ℕ} (hs : Syntax S d (List.ofFn f))
    (hi : (f i).marker=.full) (j : Fin (S.count (region f i hs hi).task).val) :
    (((region f i hs hi).plan S).payload j).total =
      Verification.total S f i ((region f i hs hi).clauseIndex S j) := by
  classical
  change (∑ k : Fin (size f i), (f (offset f i k)).delta
      (S.clause (f i).metadata.task ((region f i hs hi).clauseIndex S j))) = _
  rw [sum_offset f i (fun k => (f k).delta (S.clause (f i).metadata.task
    ((region f i hs hi).clauseIndex S j)))]
  simp [members,Finset.sum_filter,Verification.total,Verification.sum]

lemma region_holds {S : Schedule q} {d : ℕ} (hs : Syntax S d (List.ofFn f))
    (hi : (f i).marker=.full) (hg : Verification.Good S f i)
    (hp : (f i).head.phase=.success) : ∀ j, ((region f i hs hi).plan S).Holds j := by
  intro j
  have ht := (Verification.good_success S hg hp).2
  change (S.clause (f i).metadata.task ((region f i hs hi).clauseIndex S j)).truth _=true
  rw [total_region f i hs hi j]
  exact ht _ j.isLt

end Component

namespace Cell

def positionRank (c : Cell q) : ℕ := match c.pos with
  | .core p => p.val | .palette _ => q | .stop => q+1

def progress (c : Cell q) : ℕ := c.metadata.block.val*(q+2)+c.positionRank

omit [NeZero q] in
lemma rank_lt (c : Cell q) : c.positionRank < q+2 := by
  cases hp : c.pos <;> simp only [positionRank,hp]
  · rename_i p; have := p.isLt; omega
  · omega
  · omega

omit [NeZero q] in
lemma progress_mod (c : Cell q) : c.progress % (q+2)=c.positionRank := by
  simp [progress,Nat.add_mod,Nat.mod_eq_of_lt c.rank_lt]

omit [NeZero q] in
lemma progress_div (c : Cell q) : c.progress / (q+2)=c.metadata.block.val := by
  rw [progress,Nat.add_comm,Nat.add_mul_div_right _ _ (by omega)]
  simp [Nat.div_eq_of_lt c.rank_lt]

lemma progress_step {a b : Cell q} (ha : Skeleton.Structural a.skeleton b.skeleton)
    (hb : Skeleton.Internal a.skeleton b.skeleton) :
    a.progress ≤ b.progress ∧ b.progress ≤ a.progress+1 ∧
      (a.progress=b.progress → a.isPalette ∧ b.isPalette) := by
  rcases hb with ⟨_,_,hb,_,_⟩
  cases hp : a.skeleton.pos <;> cases hq : b.skeleton.pos <;>
    simp_all [Skeleton.Structural,positionRank,progress,pos,metadata,isPalette,Nat.mul_add] <;>
    try omega
  all_goals
    have hh := congrArg (fun n => n*q) hb
    simp only [Nat.add_mul,Nat.one_mul] at hh
    omega

end Cell

namespace Region
variable {d : ℕ} (R : Region q d)

lemma progress_step (a b : Fin R.size) (hab : a.val+1=b.val) :
    (R.cell a).progress ≤ (R.cell b).progress ∧
      (R.cell b).progress ≤ (R.cell a).progress+1 ∧
      ((R.cell a).progress=(R.cell b).progress → (R.cell a).isPalette ∧ (R.cell b).isPalette) := by
  exact Cell.progress_step (R.adjacent a b hab).1 (R.adjacent a b hab).2

lemma progress_mono : Monotone (fun i => (R.cell i).progress) := by
  intro i j hij
  generalize hdiff : j.val-i.val=n
  induction n generalizing j with
  | zero =>
    have he : i=j := Fin.ext (by omega)
    simp [he]
  | succ n ih =>
    let p : Fin R.size := ⟨j.val-1,by have := j.isLt; omega⟩
    have hp : p.val+1=j.val := by dsimp [p]; omega
    have hip : i≤p := by change i.val≤j.val-1; omega
    have hn : p.val-i.val=n := by dsimp [p]; omega
    exact (ih (j:=p) hip hn).trans (R.progress_step p j hp).1

omit [NeZero q] in
lemma first_progress : (R.cell R.first).progress=0 := by
  obtain ⟨hb,p,hp,hz⟩ := R.first_first
  simp [Cell.progress,Cell.positionRank,Cell.metadata,Cell.pos,hb,hp,hz]

omit [NeZero q] in
lemma last_progress : (R.cell R.last).progress=(R.task.arity.val+1)*(q+2)-1 := by
  obtain ⟨hb,hp⟩ := R.last_last
  have ht := congrArg Task.arity (R.task_eq R.last)
  change (R.cell R.last).skeleton.metadata.arity=R.task.arity at ht
  simp [Cell.progress,Cell.positionRank,Cell.metadata,Cell.pos,hp,hb,ht,Nat.add_mul]

lemma progress_surjective (r : ℕ) (hr : r≤(R.cell R.last).progress) :
    ∃ i, (R.cell i).progress=r := by
  classical
  let s := Finset.univ.filter (fun i => r≤(R.cell i).progress)
  have hs : s.Nonempty := ⟨R.last,by simp [s,hr]⟩
  let i := s.min' hs
  have hi : r≤(R.cell i).progress := (Finset.mem_filter.mp (Finset.min'_mem s hs)).2
  refine ⟨i,?_⟩
  by_cases h0 : i.val=0
  · have he : i=R.first := Fin.ext h0
    have hr0 : r=0 := by simpa [he,R.first_progress] using hi
    simp [he,R.first_progress,hr0]
  · let j : Fin R.size := ⟨i.val-1,by have := i.isLt; omega⟩
    have hj : j.val+1=i.val := by dsimp [j]; omega
    have hn : ¬r≤(R.cell j).progress := by
      intro hh
      have hm : j∈s := by simp [s,hh]
      have hle : i≤j := Finset.min'_le s _ hm
      dsimp [j] at hle
      omega
    have hu := (R.progress_step j i hj).2.1
    omega

lemma core_unique (i j : Fin R.size) (hi : (R.cell i).isCore)
    (hh : (R.cell i).progress=(R.cell j).progress) : i=j := by
  have forward (a b : Fin R.size) (hab : a.val < b.val)
      (hc : (R.cell a).progress=(R.cell b).progress) : (R.cell a).isPalette := by
    let k : Fin R.size := ⟨a.val+1,by have := b.isLt; omega⟩
    have hk := R.progress_step a k rfl
    have hm := R.progress_mono (show k≤b by change a.val+1≤b.val; omega)
    change (R.cell k).progress≤(R.cell b).progress at hm
    exact (hk.2.2 (by omega)).1
  apply Fin.ext
  by_contra hn
  have hnp : ¬(R.cell i).isPalette := by
    obtain ⟨p,hp⟩ := hi
    simp [Cell.isPalette,hp]
  by_cases hij : i.val < j.val
  · exact hnp (forward i j hij hh)
  · have hp := forward j i (by omega) hh.symm
    have hm := congrArg (fun n => n%(q+2)) hh
    rw [Cell.progress_mod,Cell.progress_mod] at hm
    obtain ⟨p,hpi⟩ := hi
    obtain ⟨x,hx⟩ := hp
    simp [Cell.positionRank,hpi,hx] at hm
    exact (Nat.ne_of_lt p.isLt) hm

omit [NeZero q] in
lemma core_rank_le (b : Fin (R.task.arity.val+1)) (p : Fin q) :
    b.val*(q+2)+p.val≤(R.cell R.last).progress := by
  rw [R.last_progress,Nat.add_mul,Nat.one_mul]
  have hb : b.val≤R.task.arity.val := by have := b.isLt; omega
  have hm := Nat.mul_le_mul_right (q+2) hb
  have := p.isLt
  omega

noncomputable def locate (b : Fin (R.task.arity.val+1)) (p : Fin q) : Fin R.size :=
  Classical.choose (R.progress_surjective (b.val*(q+2)+p.val) (R.core_rank_le b p))
lemma locate_progress (b : Fin (R.task.arity.val+1)) (p : Fin q) :
    (R.cell (R.locate b p)).progress=b.val*(q+2)+p.val :=
  Classical.choose_spec (R.progress_surjective _ (R.core_rank_le b p))
lemma locate_rank (b : Fin (R.task.arity.val+1)) (p : Fin q) :
    (R.cell (R.locate b p)).positionRank=p.val := by
  have hh := congrArg (fun n => n%(q+2)) (R.locate_progress b p)
  simpa [Cell.progress_mod,Nat.add_mod,Nat.mod_eq_of_lt (show p.val < q+2 by have := p.isLt; omega)] using hh
lemma locate_pos (b : Fin (R.task.arity.val+1)) (p : Fin q) :
    (R.cell (R.locate b p)).pos=.core p := by
  have hh := R.locate_rank b p
  cases hp : (R.cell (R.locate b p)).pos with
  | core r =>
    simp only [Cell.positionRank,hp] at hh
    exact congrArg Position.core (Fin.ext hh)
  | palette x => simp only [Cell.positionRank,hp] at hh; have := p.isLt; omega
  | stop => simp only [Cell.positionRank,hp] at hh; have := p.isLt; omega
lemma locate_block (b : Fin (R.task.arity.val+1)) (p : Fin q) :
    (R.cell (R.locate b p)).metadata.block.val=b.val := by
  have hh := congrArg (fun n => n/(q+2)) (R.locate_progress b p)
  have hx : (b.val*(q+2)+p.val)/(q+2)=b.val := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ (by omega)]
    simp [Nat.div_eq_of_lt (show p.val < q+2 by have := p.isLt; omega)]
  exact (Cell.progress_div _).symm.trans (hh.trans hx)

lemma locate_unique (b : Fin (R.task.arity.val+1)) (p : Fin q) (i : Fin R.size)
    (hb : (R.cell i).metadata.block.val=b.val) (hp : (R.cell i).pos=.core p) : i=R.locate b p := by
  apply R.core_unique i (R.locate b p) ⟨p,hp⟩
  rw [R.locate_progress]
  simp [Cell.progress,Cell.positionRank,hp,hb]

noncomputable def slot (s : Bool) (b : Fin (R.task.arity.val+1)) (p : Fin q) : ZMod 2 :=
  (R.cell (R.locate b p)).data s
noncomputable def certificate (p : Fin q) : ZMod 2 := (R.cell (R.locate 0 p)).certificate
noncomputable def read : Address q → ZMod 2
  | .data s b p => if h : b.val < R.task.arity.val+1 then R.slot s ⟨b.val,h⟩ p else 0
  | .certificate p => R.certificate p

omit [NeZero q] in
lemma block_lt (i : Fin R.size) : (R.cell i).metadata.block.val < R.task.arity.val+1 := by
  have hh := (R.cell i).metadata.block.isLt
  have ht := congrArg Task.arity (R.task_eq i)
  change (R.cell i).metadata.arity=R.task.arity at ht
  have hv := congrArg Fin.val ht
  omega

lemma sum_read (a : Address q) : (∑ i, (R.cell i).read a) = R.read a := by
  classical
  cases a with
  | data s b p =>
    by_cases hb : b.val < R.task.arity.val+1
    · let b' : Fin (R.task.arity.val+1) := ⟨b.val,hb⟩
      rw [Finset.sum_eq_single (R.locate b' p)]
      · simp [Cell.read,R.locate_pos,R.locate_block,read,hb,slot,b']
      · intro i hi hne
        cases hp : (R.cell i).pos with
        | core r =>
          simp only [Cell.read,hp]
          split
          · rename_i hh
            exact (hne (R.locate_unique b' p i hh.1 (by simpa [hh.2] using hp))).elim
          · rfl
        | palette x => simp [Cell.read,hp]
        | stop => simp [Cell.read,hp]
      · simp
    · have hi (i : Fin R.size) : (R.cell i).read (.data s b p)=0 := by
        cases hp : (R.cell i).pos with
        | core r =>
          have hh : (R.cell i).metadata.block.val≠b.val := by have := R.block_lt i; omega
          simp [Cell.read,hp,hh]
        | palette x => simp [Cell.read,hp]
        | stop => simp [Cell.read,hp]
      simp [hi,read,hb]
  | certificate p =>
    rw [Finset.sum_eq_single (R.locate 0 p)]
    · simp [Cell.read,R.locate_pos,R.locate_block,read,certificate]
    · intro i hi hne
      cases hp : (R.cell i).pos with
      | core r =>
        simp only [Cell.read,hp]
        split
        · rename_i hh
          exact (hne (R.locate_unique 0 p i hh.1 (by simpa [hh.2] using hp))).elim
        · rfl
      | palette x => simp [Cell.read,hp]
      | stop => simp [Cell.read,hp]
    · simp

lemma addressed_total (C : Clause q) : (∑ i, (R.cell i).delta C) = fun k => R.read (C.address k) := by
  funext k
  simp only [Finset.sum_apply,Cell.delta]
  exact R.sum_read (C.address k)

lemma holds_iff (S : Schedule q) (j : Fin (S.count R.task).val) :
    (R.plan S).Holds j ↔
      (S.clause R.task (R.clauseIndex S j)).truth (fun k => R.read ((S.clause R.task (R.clauseIndex S j)).address k))=true := by
  change (S.clause R.task (R.clauseIndex S j)).truth (∑ i, (R.cell i).delta _)=true ↔ _
  rw [R.addressed_total]

end Region
end SourceBurnside.FiniteTable

end

end OAI
