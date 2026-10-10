import Mathlib
import OAI.GroupTheory.PeriodicGroups.Rules.ConnectedWords

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q N : ℕ} [NeZero q]
namespace Verification
open scoped BigOperators
variable (S : Schedule q)
lemma binary_acquire_good {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i j : Fin N} (hb : BinaryAt S f g i j) {a b : Cell q} {s : Bool}
    (hfi : f i=a.boundary s) (hfj : f j=b.idle s)
    (hgi : g i=a.wing .left) (hgj : g j=b.boundary s) : AllGood S f ↔ AllGood S g := by
  apply allGood_pair S i j hb.off _ (by
    simp [hfi,hfj,hgi,hgj,Cell.marker,Cell.boundary,Cell.wing,Cell.idle,Skeleton.mark])
  intro h hi hj hh
  have ha : ¬SameRegion f h i := by
    intro hc
    exact hi (hf.unique_head (Or.inr hh) (Or.inl (by simp [hfi,Cell.boundary,Skeleton.mark])) hc)
  have hb' : ¬SameRegion f h j := by
    intro hc
    exact hj (hf.idle_component (by simp [hfj,Cell.marker,Cell.idle]) hc)
  have hcuts : ∀ h, h≠i → (cellCut f h ↔ cellCut g h) := hb.cuts_off (by
    simp [cellCut,hfj,hgj,Cell.idle,Cell.boundary,Skeleton.rightExternal,Skeleton.mark])
  have hcomp (k : Fin N) : SameRegion f h k ↔ SameRegion g h k :=
    Connected.edit_unrelated hb.adjacent hcuts ha hb'
  have hh' : (g h).skeleton.IsHead := by rw [←hb.off h hi hj]; exact Or.inr hh
  have hs := sum_congr S hf hg (Or.inr hh) hh' hcomp
    (congrArg (fun c : Cell q => c.metadata.task) (hb.off h hi hj)) hb.reads
  exact good_congr S (congrArg (fun c : Cell q => c.metadata.task) (hb.off h hi hj))
    (congrArg Cell.head (hb.off h hi hj)) (fun t => hs t N) (fun t => hs t h.val)

lemma binary_read_left_good {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i j : Fin N} (hb : BinaryAt S f g i j) {a b : Cell q} {s : Bool} {c : Fin q} {r : Reg}
    (hp : Skeleton.Pair (a.skeleton.mark .full) (b.skeleton.mark .right))
    (hfi : f i=a.wing .left) (hfj : f j=b.full s c .readLeft r)
    (hgi : g i=a.full s c .readLeft (r+a.delta (S.clause a.metadata.task c)))
    (hgj : g j=b.wing .right) : AllGood S f ↔ AllGood S g := by
  have hc : ∀ h, cellCut f h ↔ cellCut g h := hb.cuts
    (by simp [cellCut,hfi,hgi,Cell.wing,Cell.full,Skeleton.rightExternal,full_conditions hp])
    (by simp [cellCut,hfj,hgj,Cell.wing,Cell.full,Skeleton.rightExternal])
  have hconn : SameRegion f i j := (Connected.adjacent_iff hb.adjacent).mpr (by
    simp [cellCut,hfi,Cell.wing,Skeleton.rightExternal])
  have ht := SameRegion.task hf hconn.symm
  have ht' : (f j).metadata.task=(g i).metadata.task := by
    simpa [hfi,hgi,Cell.wing,Cell.full,Cell.metadata,Skeleton.mark] using ht
  obtain ⟨hT,hL⟩ := move_sums S hf hg hb.adjacent
    (h:=j) (k:=i) (by simp [hfj,Cell.full,Skeleton.IsHead])
    (by simp [hgi,Cell.full,Skeleton.IsHead]) hc hconn.symm hconn.symm ht' hb.reads
  have hdelta : (f i).delta (S.clause (f j).metadata.task c)=a.delta (S.clause a.metadata.task c) := by
    rw [ht,hfi]
    rfl
  have hL' : leftSum S f j c=leftSum S g i c+a.delta (S.clause a.metadata.task c) := by
    simpa only [leftSum,hdelta] using hL c
  apply allGood_binary_cuts S hf hg hb hc
  simpa only [hfi,hfj,hgi,hgj,Cell.marker,Cell.wing,Cell.full,Skeleton.mark_marker,
    reduceCtorEq,false_implies,true_implies,true_and,and_true] using
    good_read_left S hfj hgi ht' hT hL'

lemma binary_read_right_good {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i j : Fin N} (hb : BinaryAt S f g i j) {a b : Cell q} {s : Bool} {c : Fin q} {r : Reg}
    (hp : Skeleton.Pair (a.skeleton.mark .full) (b.skeleton.mark .right))
    (hfi : f i=a.full s c .readRight r) (hfj : f j=b.wing .right)
    (hgi : g i=a.wing .left) (hgj : g j=b.full s c .readRight r) : AllGood S f ↔ AllGood S g := by
  have hc : ∀ h, cellCut f h ↔ cellCut g h := hb.cuts
    (by simp [cellCut,hfi,hgi,Cell.wing,Cell.full,Skeleton.rightExternal,full_conditions hp])
    (by simp [cellCut,hfj,hgj,Cell.wing,Cell.full,Skeleton.rightExternal])
  have hconn : SameRegion f i j := (Connected.adjacent_iff hb.adjacent).mpr (by
    simp [cellCut,hfi,Cell.full,Skeleton.rightExternal,full_conditions hp])
  have ht := SameRegion.task hf hconn
  have ht' : (f i).metadata.task=(g j).metadata.task := by
    simpa [hfj,hgj,Cell.wing,Cell.full,Cell.metadata,Skeleton.mark] using ht
  obtain ⟨hT,_⟩ := move_sums S hf hg hb.adjacent
    (h:=i) (k:=j) (by simp [hfi,Cell.full,Skeleton.IsHead])
    (by simp [hgj,Cell.full,Skeleton.IsHead]) hc hconn (Connected.refl _ _) ht' hb.reads
  have he := good_other_move S ht' (by simp [hfi,hgj,Cell.full])
    (Or.inl (by simp [hfi,Cell.full])) hT
  apply allGood_binary_cuts S hf hg hb hc
  simpa only [hfi,hfj,hgi,hgj,Cell.marker,Cell.wing,Cell.full,Skeleton.mark_marker,
    reduceCtorEq,false_implies,true_implies,true_and,and_true] using he

lemma binary_undo_left_good {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i j : Fin N} (hb : BinaryAt S f g i j) {a b : Cell q} {s : Bool} {c : Fin q} {r : Reg}
    (hp : Skeleton.Pair (a.skeleton.mark .full) (b.skeleton.mark .right))
    (hfi : f i=a.wing .left) (hfj : f j=b.full s c .undoLeft r)
    (hgi : g i=a.full s c .undoLeft r) (hgj : g j=b.wing .right) : AllGood S f ↔ AllGood S g := by
  have hc : ∀ h, cellCut f h ↔ cellCut g h := hb.cuts
    (by simp [cellCut,hfi,hgi,Cell.wing,Cell.full,Skeleton.rightExternal,full_conditions hp])
    (by simp [cellCut,hfj,hgj,Cell.wing,Cell.full,Skeleton.rightExternal])
  have hconn : SameRegion f i j := (Connected.adjacent_iff hb.adjacent).mpr (by
    simp [cellCut,hfi,Cell.wing,Skeleton.rightExternal])
  have ht := SameRegion.task hf hconn.symm
  have ht' : (f j).metadata.task=(g i).metadata.task := by
    simpa [hfi,hgi,Cell.wing,Cell.full,Cell.metadata,Skeleton.mark] using ht
  have hs := moving_sum_congr S hf hg (h:=j) (k:=i)
    (by simp [hfj,Cell.full,Skeleton.IsHead]) (by simp [hgi,Cell.full,Skeleton.IsHead])
    hc hconn.symm ht' hb.reads
  have he := good_other_move S ht' (by simp [hfj,hgi,Cell.full])
    (Or.inr (by simp [hfj,Cell.full])) (fun t => hs t N)
  apply allGood_binary_cuts S hf hg hb hc
  simpa only [hfi,hfj,hgi,hgj,Cell.marker,Cell.wing,Cell.full,Skeleton.mark_marker,
    reduceCtorEq,false_implies,true_implies,true_and,and_true] using he

lemma binary_undo_right_good {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i j : Fin N} (hb : BinaryAt S f g i j) {a b : Cell q} {s : Bool} {c : Fin q} {r : Reg}
    (hp : Skeleton.Pair (a.skeleton.mark .full) (b.skeleton.mark .right))
    (hfi : f i=a.full s c .undoRight r) (hfj : f j=b.wing .right)
    (hgi : g i=a.wing .left)
    (hgj : g j=b.full s c .undoRight (r+a.delta (S.clause a.metadata.task c))) :
    AllGood S f ↔ AllGood S g := by
  have hc : ∀ h, cellCut f h ↔ cellCut g h := hb.cuts
    (by simp [cellCut,hfi,hgi,Cell.wing,Cell.full,Skeleton.rightExternal,full_conditions hp])
    (by simp [cellCut,hfj,hgj,Cell.wing,Cell.full,Skeleton.rightExternal])
  have hconn : SameRegion f i j := (Connected.adjacent_iff hb.adjacent).mpr (by
    simp [cellCut,hfi,Cell.full,Skeleton.rightExternal,full_conditions hp])
  have ht := SameRegion.task hf hconn
  have ht' : (f i).metadata.task=(g j).metadata.task := by
    simpa [hfj,hgj,Cell.wing,Cell.full,Cell.metadata,Skeleton.mark] using ht
  have hs := moving_sum_congr S hf hg (h:=i) (k:=j)
    (by simp [hfi,Cell.full,Skeleton.IsHead]) (by simp [hgj,Cell.full,Skeleton.IsHead])
    hc hconn ht' hb.reads
  have hL : leftSum S g j c=leftSum S f i c+a.delta (S.clause a.metadata.task c) := by
    unfold leftSum
    rw [←hs,←hb.adjacent,sum_succ,ite_eq_left (Connected.refl _ _)]
    rw [hfi]
    rfl
  have he := good_undo_right S hfi hgj ht' (fun t => hs t N) hL
  apply allGood_binary_cuts S hf hg hb hc
  simpa only [hfi,hfj,hgi,hgj,Cell.marker,Cell.wing,Cell.full,Skeleton.mark_marker,
    reduceCtorEq,false_implies,true_implies,true_and,and_true] using he

lemma allGood_binary_fields {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i j : Fin N} (hb : BinaryAt S f g i j)
    (hci : cellCut f i ↔ cellCut g i) (hcj : cellCut f j ↔ cellCut g j)
    (hmi : (f i).marker=(g i).marker) (hmj : (f j).marker=(g j).marker)
    (hti : (f i).metadata.task=(g i).metadata.task) (htj : (f j).metadata.task=(g j).metadata.task)
    (hhi : (f i).head=(g i).head) (hhj : (f j).head=(g j).head) :
    AllGood S f ↔ AllGood S g := by
  apply allGood_fields S hf hg (hb.cuts hci hcj) hb.reads
  all_goals
    intro h
    by_cases he : h=i
    · subst h; assumption
    · by_cases he' : h=j
      · subst h; assumption
      · rw [hb.off h he he']

lemma allGood_binary {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i j : Fin N} (hb : BinaryAt S f g i j) : AllGood S f ↔ AllGood S g := by
  have he := hb.edge
  generalize hfi : f i=a at he
  generalize hfj : f j=b at he
  generalize hgi : g i=a' at he
  generalize hgj : g j=b' at he
  cases he with
  | acquire a b s hp => exact binary_acquire_good S hf hg hb hfi hfj hgi hgj
  | read_left a b s c r hp => exact binary_read_left_good S hf hg hb hp hfi hfj hgi hgj
  | read_right a b s c r hp => exact binary_read_right_good S hf hg hb hp hfi hfj hgi hgj
  | undo_left a b s c r hp => exact binary_undo_left_good S hf hg hb hp hfi hfj hgi hgj
  | undo_right a b s c r hp => exact binary_undo_right_good S hf hg hb hp hfi hfj hgi hgj
  | checker_create a b p x ha hp hb' =>
    apply allGood_binary_fields S hf hg hb <;> simp [hfi,hfj,hgi,hgj,cellCut,Cell.setChecker,
      Cell.marker,Cell.metadata]
  | checker_advance a b v x ha hb' hv =>
    apply allGood_binary_fields S hf hg hb <;> simp [hfi,hfj,hgi,hgj,cellCut,Cell.setChecker,
      Cell.marker,Cell.metadata]
  | swap a b x y ha hb' hab hna hnb =>
    have hcut : a.skeleton.rightExternal ↔ b.skeleton.rightExternal := by
      rw [←hab]
      simp [Skeleton.rightExternal,Skeleton.last,Cell.setColor,Cell.pos] at ha ⊢
      simp [ha]
    have hcuts := hb.cuts (by simpa [cellCut,hfi,hgi] using hcut)
      (by simpa [cellCut,hfj,hgj] using hcut.symm)
    apply allGood_binary_cuts S hf hg hb hcuts
    have hna' : a.marker≠.full := fun hh => hna.1 (Or.inr hh)
    have hnb' : b.marker≠.full := fun hh => hnb.1 (Or.inr hh)
    simp [hfi,hfj,hgi,hgj,hna',hnb']

omit [NeZero q] in
lemma allGood_cast {M : ℕ} (he : M=N) (f : Fin M → Cell q) :
    AllGood S (fun i : Fin N => f (Fin.cast he.symm i)) ↔ AllGood S f := by
  subst N
  rfl

def WordGood (w : List (Cell q)) : Prop := AllGood S w.get

omit [NeZero q] in
lemma wordGood_ofFn (f : Fin N → Cell q) : WordGood S (List.ofFn f) ↔ AllGood S f := by
  unfold WordGood
  have he : (List.ofFn f).get = fun i => f (Fin.cast (List.length_ofFn) i) := by
    funext i; exact List.get_ofFn f i
  rw [he]
  exact allGood_cast S (List.length_ofFn).symm f

lemma coherent_of_syntax {f : Fin N → Cell q} {d : ℕ} (hf : Syntax S d (List.ofFn f)) : Coherent f := by
  have hh := Skeleton.closed_pair_chain hf.1
  rw [List.map_ofFn,List.isChain_ofFn] at hh
  intro i j hij
  have hj : i.val+1<N := by omega
  have h' := hh i.val hj
  simpa only [show (⟨i.val,by omega⟩ : Fin N)=i from Fin.ext rfl,
    show (⟨i.val+1,hj⟩ : Fin N)=j from Fin.ext hij,Function.comp_apply] using h'

omit [NeZero q] in
lemma get_of_context {f : Fin N → Cell q} {p s a : List (Cell q)}
    (hf : List.ofFn f=p++a++s) (i : Fin N) (k : ℕ) (hk : k < a.length)
    (hi : i.val=p.length+k) : f i=a[k] := by
  have hh := congrArg (fun l : List (Cell q) => l[i.val]?) hf
  simp only [List.getElem?_ofFn,dite_eq_left i.isLt,List.append_assoc] at hh
  have hn : ¬ i.val < p.length := by omega
  have he : i.val-p.length=k := by omega
  rw [List.getElem?_append,ite_eq_right hn,he,List.getElem?_append,
    ite_eq_left hk,List.getElem?_eq_getElem hk] at hh
  exact Option.some.inj hh

omit [NeZero q] in
lemma off_of_context {f g : Fin N → Cell q} {p s a b : List (Cell q)}
    (hf : List.ofFn f=p++a++s) (hg : List.ofFn g=p++b++s) (hab : a.length=b.length)
    (i : Fin N) (hi : i.val < p.length ∨ p.length+a.length ≤ i.val) : f i=g i := by
  have hf' := congrArg (fun l : List (Cell q) => l[i.val]?) hf
  have hg' := congrArg (fun l : List (Cell q) => l[i.val]?) hg
  simp only [List.getElem?_ofFn,dite_eq_left i.isLt,List.append_assoc] at hf' hg'
  have hh : (p++(a++s))[i.val]?=(p++(b++s))[i.val]? := by
    rcases hi with hi | hi
    · simp only [List.getElem?_append,ite_eq_left hi]
    · have hp : ¬ i.val < p.length := by omega
      have ha : ¬ i.val-p.length < a.length := by omega
      have hb : ¬ i.val-p.length < b.length := by omega
      simp only [List.getElem?_append,ite_eq_right hp,ite_eq_right hb,hab]
  exact Option.some.inj (hf'.trans (hh.trans hg'.symm))

lemma unary_context_good {f g : Fin N → Cell q} {p s : List (Cell q)} {a b : Cell q}
    (hf : Coherent f) (hg : Coherent g)
    (hfv : List.ofFn f=p++[a]++s) (hgv : List.ofFn g=p++[b]++s) (he : Unary S a b) :
    AllGood S f ↔ AllGood S g := by
  have hn := congrArg List.length hfv
  simp only [List.length_ofFn,List.length_append,List.length_singleton] at hn
  let i : Fin N := ⟨p.length,by omega⟩
  have hfi : f i=a := by simpa using get_of_context hfv i 0 (by simp) (by simp [i])
  have hgi : g i=b := by simpa using get_of_context hgv i 0 (by simp) (by simp [i])
  apply allGood_unary S hf hg (i:=i)
  constructor
  · intro h hne
    apply off_of_context hfv hgv rfl h
    have hn : h.val≠p.length := fun hh => hne (Fin.ext hh)
    simp only [List.length_singleton]
    omega
  · simpa [hfi,hgi] using he

lemma binary_context_good {f g : Fin N → Cell q} {p s : List (Cell q)} {a b a' b' : Cell q}
    (hf : Coherent f) (hg : Coherent g)
    (hfv : List.ofFn f=p++[a,b]++s) (hgv : List.ofFn g=p++[a',b']++s)
    (he : Binary S a b a' b') : AllGood S f ↔ AllGood S g := by
  have hn := congrArg List.length hfv
  simp only [List.length_ofFn,List.length_append,List.length_cons,List.length_nil] at hn
  let i : Fin N := ⟨p.length,by omega⟩
  let j : Fin N := ⟨p.length+1,by omega⟩
  have hfi : f i=a := by simpa using get_of_context hfv i 0 (by simp) (by simp [i])
  have hfj : f j=b := by simpa using get_of_context hfv j 1 (by simp) (by simp [j])
  have hgi : g i=a' := by simpa using get_of_context hgv i 0 (by simp) (by simp [i])
  have hgj : g j=b' := by simpa using get_of_context hgv j 1 (by simp) (by simp [j])
  apply allGood_binary S hf hg (i:=i) (j:=j)
  constructor
  · rfl
  · intro h hne hne'
    apply off_of_context hfv hgv rfl h
    have hni : h.val≠p.length := fun hh => hne (Fin.ext hh)
    have hnj : h.val≠p.length+1 := fun hh => hne' (Fin.ext hh)
    simp only [List.length_cons,List.length_nil]
    omega
  · simpa [hfi,hfj,hgi,hgj] using he

lemma allGood_step {f g : Fin N → Cell q} {d : ℕ} (hf : Syntax S d (List.ofFn f))
    (he : Step S d (List.ofFn f) (List.ofFn g)) : AllGood S f ↔ AllGood S g := by
  have hg := reach_syntax (Relation.ReflTransGen.single he) hf
  have hf' := coherent_of_syntax S hf
  have hg' := coherent_of_syntax S hg
  obtain ⟨p,s,v,w,hf,hg,hh⟩ := he
  rcases hh.2 with ⟨a,b,rfl,rfl,he⟩ | ⟨a,b,a',b',rfl,rfl,he⟩
  · rcases he with he | he
    · exact unary_context_good S hf' hg' hf hg he
    · exact (unary_context_good S hg' hf' hg hf he).symm
  · rcases he with he | he
    · exact binary_context_good S hf' hg' hf hg he
    · exact (binary_context_good S hg' hf' hg hf he).symm

lemma wordGood_step {v w : List (Cell q)} {d : ℕ} (hv : Syntax S d v)
    (he : Step S d v w) : WordGood S v ↔ WordGood S w := by
  let f := v.get
  have hl := step_length he
  let g : Fin v.length → Cell q := fun i => w.get (Fin.cast hl i)
  have hfv : List.ofFn f=v := List.ofFn_get v
  have hgw : List.ofFn g=w := by
    rw [show g=(fun i => w.get (Fin.cast hl i)) from rfl,←List.ofFn_congr hl.symm w.get]
    exact List.ofFn_get w
  rw [←hfv] at hv
  rw [←hfv,←hgw] at he ⊢
  rw [wordGood_ofFn,wordGood_ofFn]
  exact allGood_step S hv he

theorem wordGood_reach {v w : List (Cell q)} {d : ℕ} (hv : Syntax S d v)
    (he : Reach S d v w) : WordGood S v ↔ WordGood S w := by
  induction he with
  | refl => rfl
  | tail h e ih => exact ih.trans (wordGood_step S (reach_syntax h hv) e)

omit [NeZero q] in
lemma wordGood_idle {w : List (Cell q)} (hw : ∀ c ∈ w, c.marker=.idle) : WordGood S w := by
  apply allGood_of_idle
  intro i
  exact hw (w.get i) (List.get_mem _ _)

theorem reach_clean_good {v w : List (Cell q)} {d : ℕ}
    (hv : Syntax S d v) (hi : ∀ c ∈ v, c.marker=.idle) (he : Reach S d v w) : WordGood S w :=
  (wordGood_reach S hv he).mp (wordGood_idle S hi)

end Verification

end SourceBurnside.FiniteTable

namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q N : ℕ} [NeZero q]

namespace Connected
lemma mono {cut cut' : Fin N → Prop} {i j : Fin N}
    (hcut : ∀ k, cut' k → cut k) (h : Connected cut i j) : Connected cut' i j := by
  intro k hk hk' hc
  exact h k hk hk' (hcut k hc)
end Connected

def Own (f : Fin N → Cell q) (i h : Fin N) : Prop :=
  SameRegion f i h ∧ (f h).skeleton.IsHead

lemma BinaryAt.everywhere {S : Schedule q} {f g : Fin N → Cell q} {i j : Fin N}
    (hb : BinaryAt S f g i j) {P : Cell q → Cell q → Prop} (hrefl : ∀ a, P a a)
    (hi : P (f i) (g i)) (hj : P (f j) (g j)) : ∀ h, P (f h) (g h) := by
  intro h
  by_cases he : h=i
  · simpa [he] using hi
  · by_cases he' : h=j
    · simpa [he'] using hj
    · rw [hb.off h he he']; exact hrefl _

namespace Committed

noncomputable def value (f : Fin N → Cell q) (i : Fin N) : ZMod 2 := by
  classical
  exact if (f i).marker=.idle then (f i).data false
    else if h : ∃ k, Own f i k then (f i).data (f (Classical.choose h)).head.side else 0

omit [NeZero q] in
lemma idle {f : Fin N → Cell q} {i : Fin N} (hi : (f i).marker=.idle) :
    value f i=(f i).data false := by simp [value,hi]

omit [NeZero q] in
lemma owned {f : Fin N → Cell q} (hf : Coherent f) {i h : Fin N} (hh : Own f i h) :
    value f i=(f i).data (f h).head.side := by
  classical
  have hi : (f i).marker≠.idle := hf.region_locked hh.2 hh.1
  have he : ∃ k, Own f i k := ⟨h,hh⟩
  have hch := Classical.choose_spec he
  have heq : Classical.choose he=h :=
    hf.unique_head hch.2 hh.2 (hch.1.symm.trans hh.1)
  simp only [value,ite_eq_right hi,dite_eq_left he,heq]

omit [NeZero q] in
lemma congr {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g) (i : Fin N)
    (hi : (f i).marker=.idle ↔ (g i).marker=.idle)
    (hdi : (f i).marker=.idle → (f i).data false=(g i).data false)
    (ho : ∀ h, Own f i h → ∃ k, Own g i k ∧ (f i).data (f h).head.side=(g i).data (g k).head.side)
    (hn : (∃ k, Own g i k) → ∃ h, Own f i h) : value f i=value g i := by
  classical
  by_cases hid : (f i).marker=.idle
  · rw [idle hid,idle (hi.mp hid)]
    exact hdi hid
  · by_cases he : ∃ h, Own f i h
    · obtain ⟨h,hh⟩ := he
      obtain ⟨k,hk,heq⟩ := ho h hh
      rw [owned hf hh,owned hg hk]
      exact heq
    · have he' : ¬∃ k, Own g i k := fun hh => he (hn hh)
      simp only [value,ite_eq_right hid,ite_eq_right ((not_congr hi).mp hid),dite_eq_right he,dite_eq_right he']

omit [NeZero q] in
lemma fields {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g) (i : Fin N)
    (hc : ∀ h, SameRegion f i h ↔ SameRegion g i h)
    (hi : (f i).marker=.idle ↔ (g i).marker=.idle)
    (hd : (f i).data=(g i).data)
    (hh : ∀ h, SameRegion f i h → ((f h).skeleton.IsHead ↔ (g h).skeleton.IsHead))
    (hs : ∀ h, Own f i h → (f h).head.side=(g h).head.side) : value f i=value g i := by
  apply congr hf hg i hi (fun _ => congrFun hd false)
  · intro h ho
    exact ⟨h,⟨(hc h).mp ho.1,(hh h ho.1).mp ho.2⟩,by rw [hd,hs h ho]⟩
  · rintro ⟨h,hh'⟩
    have hhc := (hc h).mpr hh'.1
    exact ⟨h,hhc,(hh h hhc).mpr hh'.2⟩

omit [NeZero q] in
lemma same_cuts_fields {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    (hc : ∀ i, cellCut f i ↔ cellCut g i)
    (hi : ∀ i, (f i).marker=.idle ↔ (g i).marker=.idle)
    (hd : ∀ i, (f i).data=(g i).data)
    (hh : ∀ i, (f i).skeleton.IsHead ↔ (g i).skeleton.IsHead)
    (hs : ∀ i, (f i).skeleton.IsHead → (f i).head.side=(g i).head.side) :
    ∀ i, value f i=value g i := by
  intro i
  exact fields hf hg i (fun _ => Connected.congr hc) (hi i) (hd i)
    (fun h _ => hh h) (fun h ho => hs h ho.2)

lemma unary_fields {S : Schedule q} {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i : Fin N} (hu : UnaryAt S f g i)
    (hi : (f i).marker=.idle ↔ (g i).marker=.idle) (hd : (f i).data=(g i).data)
    (hh : (f i).skeleton.IsHead ↔ (g i).skeleton.IsHead)
    (hs : (f i).head.side=(g i).head.side) : ∀ h, value f h=value g h := by
  apply same_cuts_fields hf hg hu.cuts
  all_goals
    intro h
    by_cases he : h=i
    · subst h; first | exact hi | exact hd | exact hh | exact fun _ => hs
    · simp only [hu.off h he,implies_true]

lemma unary_create {S : Schedule q} {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i : Fin N} (hu : UnaryAt S f g i) {a : Cell q} {s : Bool}
    (hfi : f i=a.idle s) (hgi : g i=a.boundary s) : ∀ h, value f h=value g h := by
  intro h
  by_cases he : h=i
  · subst h
    rw [idle (by simp [hfi,Cell.idle,Cell.marker]),
      owned hg (h:=i) ⟨Connected.refl _ _,Or.inl (by simp [hgi,Cell.boundary,Skeleton.mark])⟩]
    simp [hfi,hgi,Cell.idle,Cell.boundary,defaultHead]
  · have hic : ¬SameRegion f h i := fun hc => he (hf.idle_component
      (by simp [hfi,Cell.idle,Cell.marker]) hc)
    apply fields hf hg h (fun _ => Connected.congr hu.cuts)
      (by rw [hu.off h he]) (congrArg Cell.data (hu.off h he))
    · intro k hk
      have hki : k≠i := by intro heq; subst k; exact hic hk
      rw [hu.off k hki]
    · intro k hk
      have hki : k≠i := by intro heq; subst k; exact hic hk.1
      rw [hu.off k hki]

def UnaryNonPivot (S : Schedule q) (a b : Cell q) : Prop :=
  Unary S a b ∧ ¬ (a.marker=.full ∧ a.head.phase=.success ∧ a.head.side≠b.head.side)

lemma unary_nonpivot {S : Schedule q} {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i : Fin N} (hu : UnaryAt S f g i)
    (hn : ¬ ((f i).marker=.full ∧ (f i).head.phase=.success ∧ (f i).head.side≠(g i).head.side)) :
    ∀ h, value f h=value g h := by
  have he := hu.edge
  generalize hfi : f i=a at he
  generalize hgi : g i=b at he
  cases he with
  | create c s hc => exact unary_create hf hg hu hfi hgi
  | pivot c s hl ht =>
    exfalso
    apply hn
    simp [hfi,hgi,Cell.full,Cell.marker,Skeleton.mark]
  | _ =>
    apply unary_fields hf hg hu <;>
      simp [hfi,hgi,Cell.full,Cell.boundary,Cell.marker,Skeleton.IsHead,Skeleton.mark,defaultHead]

omit [NeZero q] in
lemma moving_head {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i j : Fin N} (hc : ∀ h, cellCut f h ↔ cellCut g h) (hconn : SameRegion f i j)
    (hhi : (f i).skeleton.IsHead) (hhj : (g j).skeleton.IsHead)
    (hoff : ∀ h, h≠i → h≠j → f h=g h)
    (hi : ∀ h, (f h).marker=.idle ↔ (g h).marker=.idle)
    (hd : ∀ h, (f h).data=(g h).data)
    (hs : (f i).head.side=(g j).head.side) : ∀ h, value f h=value g h := by
  intro h
  by_cases ho : SameRegion f h i
  · have ho' : Own g h j := ⟨(Connected.congr hc).mp (ho.trans hconn),hhj⟩
    rw [owned hf ⟨ho,hhi⟩,owned hg ho',hd,hs]
  · have ho' : ¬SameRegion f h j := fun hj => ho (hj.trans hconn.symm)
    apply fields hf hg h (fun _ => Connected.congr hc) (hi h) (hd h)
    · intro k hk
      have hki : k≠i := by intro he; subst k; exact ho hk
      have hkj : k≠j := by intro he; subst k; exact ho' hk
      rw [hoff k hki hkj]
    · intro k hk
      have hki : k≠i := by intro he; subst k; exact ho hk.1
      have hkj : k≠j := by intro he; subst k; exact ho' hk.1
      rw [hoff k hki hkj]

lemma binary_acquire {S : Schedule q} {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i j : Fin N} (hb : BinaryAt S f g i j) {a b : Cell q} {s : Bool}
    (hfi : f i=a.boundary s) (hfj : f j=b.idle s)
    (hgi : g i=a.wing .left) (hgj : g j=b.boundary s) : ∀ h, value f h=value g h := by
  have hc : ∀ h, h≠i → (cellCut f h ↔ cellCut g h) := hb.cuts_off (by
    simp [cellCut,hfj,hgj,Cell.idle,Cell.boundary,Skeleton.rightExternal,Skeleton.mark])
  have hncut : ¬cellCut g i := by simp [cellCut,hgi,Cell.wing,Skeleton.rightExternal]
  have hmono : ∀ h, cellCut g h → cellCut f h := by
    intro h hh
    by_cases he : h=i
    · subst h; exact (hncut hh).elim
    · exact (hc h he).mpr hh
  have hjoin : SameRegion g i j := (Connected.adjacent_iff hb.adjacent).mpr hncut
  have hihead : (f i).skeleton.IsHead := Or.inl (by simp [hfi,Cell.boundary,Skeleton.mark])
  have hjhead : (g j).skeleton.IsHead := Or.inl (by simp [hgj,Cell.boundary,Skeleton.mark])
  intro h
  by_cases he : h=j
  · subst h
    rw [idle (by simp [hfj,Cell.idle,Cell.marker]),owned hg ⟨Connected.refl _ _,hjhead⟩]
    simp [hfj,hgj,Cell.idle,Cell.boundary,defaultHead]
  · by_cases ho : SameRegion f h i
    · have ho' : SameRegion g h j := (ho.mono hmono).trans hjoin
      rw [owned hf ⟨ho,hihead⟩,owned hg ⟨ho',hjhead⟩]
      have hd : (f h).data=(g h).data := by
        by_cases he' : h=i
        · subst h; simp [hfi,hgi,Cell.boundary,Cell.wing]
        · rw [hb.off h he' he]
      simp only [hfi,hgj,Cell.boundary,hd]
    · have hoj : ¬SameRegion f h j := fun hh => he (hf.idle_component
        (by simp [hfj,Cell.idle,Cell.marker]) hh)
      have hc' (k : Fin N) : SameRegion f h k ↔ SameRegion g h k :=
        Connected.edit_unrelated hb.adjacent hc ho hoj
      have hni : h≠i := by intro hh; subst h; exact ho (Connected.refl _ _)
      apply fields hf hg h hc' (by rw [hb.off h hni he]) (congrArg Cell.data (hb.off h hni he))
      · intro k hk
        have hki : k≠i := by intro hh; subst k; exact ho hk
        have hkj : k≠j := by intro hh; subst k; exact hoj hk
        rw [hb.off k hki hkj]
      · intro k hk
        have hki : k≠i := by intro hh; subst k; exact ho hk.1
        have hkj : k≠j := by intro hh; subst k; exact hoj hk.1
        rw [hb.off k hki hkj]

lemma binary_fields {S : Schedule q} {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i j : Fin N} (hb : BinaryAt S f g i j)
    (hci : cellCut f i ↔ cellCut g i) (hcj : cellCut f j ↔ cellCut g j)
    (hmi : (f i).marker=.idle ↔ (g i).marker=.idle) (hmj : (f j).marker=.idle ↔ (g j).marker=.idle)
    (hdi : (f i).data=(g i).data) (hdj : (f j).data=(g j).data)
    (hhi : (f i).skeleton.IsHead ↔ (g i).skeleton.IsHead)
    (hhj : (f j).skeleton.IsHead ↔ (g j).skeleton.IsHead)
    (hsi : (f i).head.side=(g i).head.side) (hsj : (f j).head.side=(g j).head.side) :
    ∀ h, value f h=value g h := by
  apply same_cuts_fields hf hg (hb.cuts hci hcj)
  · exact hb.everywhere (P:=fun a b => a.marker=.idle ↔ b.marker=.idle) (fun _ => Iff.rfl) hmi hmj
  · exact hb.everywhere (P:=fun a b => a.data=b.data) (fun _ => rfl) hdi hdj
  · exact hb.everywhere (P:=fun a b => a.skeleton.IsHead ↔ b.skeleton.IsHead) (fun _ => Iff.rfl) hhi hhj
  · intro h _; exact hb.everywhere (P:=fun a b => a.head.side=b.head.side) (fun _ => rfl) hsi hsj h

theorem binary {S : Schedule q} {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i j : Fin N} (hb : BinaryAt S f g i j) : ∀ h, value f h=value g h := by
  have he := hb.edge
  generalize hfi : f i=a at he
  generalize hfj : f j=b at he
  generalize hgi : g i=a' at he
  generalize hgj : g j=b' at he
  cases he with
  | acquire a b s hp => exact binary_acquire hf hg hb hfi hfj hgi hgj
  | read_left a b s c r hp | undo_left a b s c r hp =>
    have hc : ∀ h, cellCut f h ↔ cellCut g h := hb.cuts
      (by simp [cellCut,hfi,hgi,Cell.wing,Cell.full,Skeleton.rightExternal,full_conditions hp])
      (by simp [cellCut,hfj,hgj,Cell.wing,Cell.full,Skeleton.rightExternal])
    have hconn : SameRegion f i j := (Connected.adjacent_iff hb.adjacent).mpr (by
      simp [cellCut,hfi,Cell.wing,Skeleton.rightExternal])
    apply moving_head hf hg hc hconn.symm
      (by simp [hfj,Cell.full,Skeleton.IsHead]) (by simp [hgi,Cell.full,Skeleton.IsHead])
      (fun h hi hj => hb.off h hj hi)
    · apply hb.everywhere (P:=fun a b => a.marker=.idle ↔ b.marker=.idle) (fun _ => Iff.rfl) <;>
        simp [hfi,hfj,hgi,hgj,Cell.marker,Cell.wing,Cell.full,Skeleton.mark]
    · apply hb.everywhere (P:=fun a b => a.data=b.data) (fun _ => rfl) <;> simp [hfi,hfj,hgi,hgj,Cell.wing,Cell.full]
    · simp [hfj,hgi,Cell.full]
  | read_right a b s c r hp | undo_right a b s c r hp =>
    have hc : ∀ h, cellCut f h ↔ cellCut g h := hb.cuts
      (by simp [cellCut,hfi,hgi,Cell.wing,Cell.full,Skeleton.rightExternal,full_conditions hp])
      (by simp [cellCut,hfj,hgj,Cell.wing,Cell.full,Skeleton.rightExternal])
    have hconn : SameRegion f i j := (Connected.adjacent_iff hb.adjacent).mpr (by
      simp [cellCut,hfi,Cell.full,Skeleton.rightExternal,full_conditions hp])
    apply moving_head hf hg hc hconn
      (by simp [hfi,Cell.full,Skeleton.IsHead]) (by simp [hgj,Cell.full,Skeleton.IsHead]) hb.off
    · apply hb.everywhere (P:=fun a b => a.marker=.idle ↔ b.marker=.idle) (fun _ => Iff.rfl) <;>
        simp [hfi,hfj,hgi,hgj,Cell.marker,Cell.wing,Cell.full,Skeleton.mark]
    · apply hb.everywhere (P:=fun a b => a.data=b.data) (fun _ => rfl) <;> simp [hfi,hfj,hgi,hgj,Cell.wing,Cell.full]
    · simp [hfi,hgj,Cell.full]
  | checker_create a b p x ha hp hb' =>
    apply binary_fields hf hg hb <;>
      simp [hfi,hfj,hgi,hgj,cellCut,Cell.setChecker,Cell.marker]
  | checker_advance a b v x ha hb' hv =>
    apply binary_fields hf hg hb <;>
      simp [hfi,hfj,hgi,hgj,cellCut,Cell.setChecker,Cell.marker]
  | swap a b x y ha hb' hab hna hnb =>
    change a.skeleton.pos=.palette x at ha
    apply binary_fields hf hg hb <;>
      simp [cellCut,hfi,hfj,hgi,hgj,←hab,Cell.setColor,Skeleton.rightExternal,Skeleton.last,
        Skeleton.IsHead,Cell.marker,ha]

def PivotAt (f g : Fin N → Cell q) (i : Fin N) : Prop :=
  ∃ (a : Cell q) (s : Bool), f i=a.full s 0 .success 0 ∧ g i=a.full (!s) 0 .success 0 ∧
    (∀ h, h≠i → f h=g h) ∧ a.skeleton.last ∧ a.metadata.zeroTask=false

lemma PivotAt.symm {f g : Fin N → Cell q} {i : Fin N} (hp : PivotAt f g i) : PivotAt g f i := by
  obtain ⟨a,s,hf,hg,ho,hl,ht⟩ := hp
  exact ⟨a,!s,hg,by simpa using hf,fun h hh => (ho h hh).symm,hl,ht⟩

lemma PivotAt.unary {S : Schedule q} {f g : Fin N → Cell q} {i : Fin N} (hp : PivotAt f g i) :
    UnaryAt S f g i := by
  obtain ⟨a,s,hf,hg,ho,hl,ht⟩ := hp
  exact ⟨ho,by simpa [hf,hg] using Unary.pivot (S:=S) a s hl ht⟩

lemma pivot {S : Schedule q} {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i : Fin N} (hu : UnaryAt S f g i) {a : Cell q} {s : Bool}
    (hfi : f i=a.full s 0 .success 0) (hgi : g i=a.full (!s) 0 .success 0) :
    (∀ h, SameRegion f h i → value f h=(f h).data s) ∧
    (∀ h, value g h=if SameRegion f h i then (f h).data (!s) else value f h) := by
  classical
  have hh : (f i).skeleton.IsHead := Or.inr (by simp [hfi,Cell.full,Skeleton.mark])
  have hk : (g i).skeleton.IsHead := Or.inr (by simp [hgi,Cell.full,Skeleton.mark])
  constructor
  · intro h ho
    simpa [hfi,Cell.full] using owned hf ⟨ho,hh⟩
  · intro h
    by_cases ho : SameRegion f h i
    · rw [ite_eq_left ho,owned hg ⟨(Connected.congr hu.cuts).mp ho,hk⟩]
      have hd : (g h).data=(f h).data := by
        by_cases he : h=i
        · subst h; simp [hfi,hgi,Cell.full]
        · rw [hu.off h he]
      simp [hgi,Cell.full,hd]
    · rw [ite_eq_right ho]
      symm
      have hni : h≠i := by intro he; subst h; exact ho (Connected.refl _ _)
      apply fields hf hg h (fun _ => Connected.congr hu.cuts)
        (by rw [hu.off h hni]) (congrArg Cell.data (hu.off h hni))
      · intro k hk
        have hki : k≠i := by intro he; subst k; exact ho hk
        rw [hu.off k hki]
      · intro k hk
        have hki : k≠i := by intro he; subst k; exact ho hk.1
        rw [hu.off k hki]

lemma unary_classified {S : Schedule q} {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i : Fin N} (hu : UnaryAt S f g i) : (∀ h, value f h=value g h) ∨ PivotAt f g i := by
  have he := hu.edge
  generalize hfi : f i=a at he
  generalize hgi : g i=b at he
  cases he with
  | pivot c s hl ht => exact Or.inr ⟨c,s,hfi,hgi,hu.off,hl,ht⟩
  | _ => exact Or.inl (unary_nonpivot hf hg hu (by
      simp [hfi,hgi,Cell.full,Cell.boundary,Cell.idle,Cell.marker,Skeleton.mark]))

lemma unaryAt_context {S : Schedule q} {f g : Fin N → Cell q} {p s : List (Cell q)} {a b : Cell q}
    (hfv : List.ofFn f=p++[a]++s) (hgv : List.ofFn g=p++[b]++s) (he : Unary S a b) :
    ∃ i, UnaryAt S f g i := by
  have hn := congrArg List.length hfv
  simp only [List.length_ofFn,List.length_append,List.length_singleton] at hn
  let i : Fin N := ⟨p.length,by omega⟩
  have hfi : f i=a := by simpa using Verification.get_of_context hfv i 0 (by simp) (by simp [i])
  have hgi : g i=b := by simpa using Verification.get_of_context hgv i 0 (by simp) (by simp [i])
  refine ⟨i,?_,by simpa [hfi,hgi] using he⟩
  intro h hne
  apply Verification.off_of_context hfv hgv rfl h
  have hn : h.val≠p.length := fun hh => hne (Fin.ext hh)
  simp only [List.length_singleton]
  omega

lemma binaryAt_context {S : Schedule q} {f g : Fin N → Cell q} {p s : List (Cell q)} {a b a' b' : Cell q}
    (hfv : List.ofFn f=p++[a,b]++s) (hgv : List.ofFn g=p++[a',b']++s)
    (he : Binary S a b a' b') : ∃ i j, BinaryAt S f g i j := by
  have hn := congrArg List.length hfv
  simp only [List.length_ofFn,List.length_append,List.length_cons,List.length_nil] at hn
  let i : Fin N := ⟨p.length,by omega⟩
  let j : Fin N := ⟨p.length+1,by omega⟩
  have hfi : f i=a := by simpa using Verification.get_of_context hfv i 0 (by simp) (by simp [i])
  have hfj : f j=b := by simpa using Verification.get_of_context hfv j 1 (by simp) (by simp [j])
  have hgi : g i=a' := by simpa using Verification.get_of_context hgv i 0 (by simp) (by simp [i])
  have hgj : g j=b' := by simpa using Verification.get_of_context hgv j 1 (by simp) (by simp [j])
  refine ⟨i,j,rfl,?_,by simpa [hfi,hfj,hgi,hgj] using he⟩
  intro h hne hne'
  apply Verification.off_of_context hfv hgv rfl h
  have hni : h.val≠p.length := fun hh => hne (Fin.ext hh)
  have hnj : h.val≠p.length+1 := fun hh => hne' (Fin.ext hh)
  simp only [List.length_cons,List.length_nil]
  omega

theorem step_classified {S : Schedule q} {f g : Fin N → Cell q} {d : ℕ}
    (hf : Syntax S d (List.ofFn f)) (he : Step S d (List.ofFn f) (List.ofFn g)) :
    (∀ h, value f h=value g h) ∨ ∃ i, PivotAt f g i := by
  have hg := reach_syntax (Relation.ReflTransGen.single he) hf
  have hf' := Verification.coherent_of_syntax S hf
  have hg' := Verification.coherent_of_syntax S hg
  obtain ⟨p,s,v,w,hf,hg,hh⟩ := he
  rcases hh.2 with ⟨a,b,rfl,rfl,he⟩ | ⟨a,b,a',b',rfl,rfl,he⟩
  · rcases he with he | he
    · obtain ⟨i,hi⟩ := unaryAt_context hf hg he
      exact (unary_classified hf' hg' hi).imp id (fun hh => ⟨i,hh⟩)
    · obtain ⟨i,hi⟩ := unaryAt_context hg hf he
      exact (unary_classified hg' hf' hi).imp (fun hh h => (hh h).symm) (fun hh => ⟨i,hh.symm⟩)
  · rcases he with he | he
    · obtain ⟨i,j,hb⟩ := binaryAt_context hf hg he
      exact Or.inl (binary hf' hg' hb)
    · obtain ⟨i,j,hb⟩ := binaryAt_context hg hf he
      exact Or.inl (fun h => (binary hg' hf' hb h).symm)

end Committed

namespace Verification
variable (S : Schedule q)

omit [NeZero q] in
lemma good_success {f : Fin N → Cell q} {i : Fin N} (hi : Good S f i)
    (hp : (f i).head.phase=.success) :
    (f i).head.reg=0 ∧ ∀ j : Fin q, j.val < (S.count (f i).metadata.task).val → holds S f i j := by
  simpa [Good,hp,potential] using hi

omit [NeZero q] in
lemma good_semanticZero_sound {f : Fin N → Cell q} {i : Fin N} (hi : Good S f i)
    (hz : SemanticZero S (f i)) :
    (f i).head.phase=.success ∧ (f i).metadata.zeroTask=true ∧ (f i).head.reg=0 ∧
      ∀ j : Fin q, j.val < (S.count (f i).metadata.task).val → holds S f i j := by
  have hh := good_semanticZero S hi hz
  exact ⟨hh.1,hh.2,(good_success S hi hh.1).1,(good_success S hi hh.1).2⟩

lemma pivot_certified {f g : Fin N → Cell q} (hf : AllGood S f) {i : Fin N}
    (hp : Committed.PivotAt f g i) :
    (f i).metadata.zeroTask=false ∧
      ∀ j : Fin q, j.val < (S.count (f i).metadata.task).val → holds S f i j := by
  obtain ⟨a,s,hfi,hgi,ho,hl,ht⟩ := hp
  exact ⟨by simpa [hfi,Cell.full,Cell.metadata,Skeleton.mark] using ht,
    (good_success S (hf i (by simp [hfi,Cell.full,Cell.marker,Skeleton.mark]))
      (by simp [hfi,Cell.full])).2⟩

end Verification
end SourceBurnside.FiniteTable

end

end OAI
