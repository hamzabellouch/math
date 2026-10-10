import OAI.Probability.FKMaps.CoreWords

namespace OAI

noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory

/-- The genuine finite ordered connected-core tree. Leaves carry exactly
the trivial word; every nonleaf has one child for each ordered core dart. -/
inductive CoreTree where
  | leaf : CoreTree
  | branch (core : Core) (children : Fin core.val.length→ CoreTree) : CoreTree

namespace CoreTree

def word : CoreTree→List TypedLetter
  | leaf => []
  | branch c ts => cornerInsert (cornerList c (fun i => (ts i).word))

lemma word_empty (t : CoreTree) : stackTypedRun t.word []=some [] := by
  induction t with
  | leaf => rfl
  | branch c ts ih =>
    apply ValidCorners.empty
    refine ⟨?_,?_⟩
    · rw [cornerList_fst];exact c.property
    · intro x hx
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
      exact ih i

lemma branch_nonempty (c : Core) (ts : Fin c.val.length→ CoreTree) : (branch c ts).word≠[] := by
  apply ValidCorners.nonempty
  refine ⟨?_,?_⟩
  · rw [cornerList_fst];exact c.property
  · intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact (ts i).word_empty

lemma word_injective : Function.Injective word := by
  intro t
  induction t with
  | leaf =>
    intro u h
    cases u with
    | leaf => rfl
    | branch c us => exact False.elim (branch_nonempty c us h.symm)
  | branch c ts ih =>
    intro u h
    cases u with
    | leaf => exact False.elim (branch_nonempty c ts h)
    | branch d us =>
      have hvc (c : Core) (ts : Fin c.val.length→ CoreTree) :
          ValidCorners (cornerList c (fun i => (ts i).word)) := by
        exact cornerList_valid c (fun i => ⟨(ts i).word,(ts i).word_empty⟩)
      have hh := valid_corner_injective (hvc c ts) (hvc d us) h
      have hcd := cornerList_congr_core hh
      subst d
      have hwords := cornerList_injective c hh
      have hts : ts=us := by
        funext i
        exact ih i (congrFun hwords i)
      rw [hts]

end CoreTree

lemma corner_child_short (l : List (TypedLetter×List TypedLetter))
    (x : TypedLetter×List TypedLetter) (hx : x∈l) : x.2.length<(cornerInsert l).length := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    change x.2.length<((y.1::y.2)++cornerInsert l).length
    simp only [List.length_append,List.length_cons]
    rcases List.mem_cons.mp hx with rfl|hx
    · omega
    · have hh := ih hx;omega

/-- The finite recursive forest construction terminates because actual
corner words are strictly shorter. -/
theorem exists_core_tree (w : List TypedLetter) (hw : stackTypedRun w []=some []) :
    ∃ t : CoreTree,t.word=w := by
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
    by_cases he : w=[]
    · exact ⟨.leaf,he.symm⟩
    let W : NonemptyTypedWord := ⟨⟨w,hw⟩,he⟩
    let d := coreChildrenEquiv.symm W
    have hd : cornerInsert (cornerList d.1 (fun i => (d.2 i).val))=w :=
      congrArg (fun w => w.val.val) (coreChildrenEquiv.apply_symm_apply W)
    have hshort (i : Fin d.1.val.length) : (d.2 i).val.length<n := by
      have hh := corner_child_short (cornerList d.1 (fun i => (d.2 i).val))
        (d.1.val.get i,(d.2 i).val) (List.mem_ofFn.mpr ⟨i,rfl⟩)
      rwa [hd,hn] at hh
    have hchild (i : Fin d.1.val.length) : ∃ t : CoreTree,t.word=(d.2 i).val :=
      ih _ (hshort i) _ (d.2 i).property rfl
    let ts := fun i => (hchild i).choose
    refine ⟨.branch d.1 ts,?_⟩
    change cornerInsert (cornerList d.1 (fun i => (ts i).word))=w
    have ht : (fun i => (ts i).word)=(fun i => (d.2 i).val) :=
      funext (fun i => (hchild i).choose_spec)
    rw [ht,hd]

namespace CoreTree

def toWord (t : CoreTree) : EmptyTypedWord := ⟨t.word,t.word_empty⟩

lemma toWord_bijective : Function.Bijective toWord := by
  constructor
  · intro t u h
    exact word_injective (congrArg Subtype.val h)
  · intro w
    obtain ⟨t,ht⟩ := exists_core_tree w.val w.property
    exact ⟨t,Subtype.ext ht⟩

/-- Full actual-word / normalized connected-core ordered-tree bijection. -/
def wordEquiv : CoreTree ≃ EmptyTypedWord := Equiv.ofBijective toWord toWord_bijective

end CoreTree
end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

/-- Ordered rooted trees; the empty child list is an actual leaf. -/
inductive PlaneTree where
  | node : List PlaneTree → PlaneTree

noncomputable instance : DecidableEq PlaneTree := Classical.decEq _
namespace PlaneTree

@[elab_as_elim] theorem inductionMem {P : PlaneTree → Prop}
    (hn : ∀ ts, (∀ t ∈ ts, P t) → P (node ts)) (t : PlaneTree) : P t :=
  PlaneTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ t ∈ ts, P t)
    hn (by simp) (by intro t ts ht hts t' ht'; rcases List.mem_cons.mp ht' with rfl | ht'; exact ht; exact hts _ ht') t

def degrees : PlaneTree → List ℕ
  | node ts => ts.length :: ts.flatMap degrees

def forestDegrees (ts : List PlaneTree) : List ℕ := ts.flatMap degrees

def build : List ℕ → List PlaneTree → List PlaneTree
  | [],ts => ts
  | k::l,ts => let fs := build l ts; node (fs.take k)::fs.drop k

lemma build_append (l l' : List ℕ) (ts : List PlaneTree) :
    build (l++l') ts=build l (build l' ts) := by
  induction l with
  | nil => rfl
  | cons k l ih => simp only [List.cons_append,build,ih]

lemma build_degrees (t : PlaneTree) (ts : List PlaneTree) : build t.degrees ts=t::ts := by
  induction t using inductionMem generalizing ts with
  | hn fs ih =>
    have hf : ∀ (fs' : List PlaneTree), (∀ f∈fs',∀ ts,build f.degrees ts=f::ts) →
        ∀ ts,build (fs'.flatMap degrees) ts=fs'++ts := by
      intro fs' hf ts
      induction fs' with
      | nil => rfl
      | cons f fs' ih' =>
        rw [List.flatMap_cons,build_append,hf f (by simp),ih' (by aesop)]
        rfl
    rw [degrees,build,hf fs (by exact ih)]
    simp

lemma build_forestDegrees (fs ts : List PlaneTree) : build (forestDegrees fs) ts=fs++ts := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    change build (degrees f++forestDegrees fs) ts=(f::fs)++ts
    rw [build_append,ih,build_degrees]
    rfl

lemma degrees_injective : Function.Injective degrees := by
  intro t t' h
  have hh := congrArg (fun l => build l []) h
  simpa only [build_degrees,List.cons.injEq,and_true] using hh

lemma forestDegrees_injective : Function.Injective forestDegrees := by
  intro fs fs' h
  have hh := congrArg (fun l => build l []) h
  simpa only [build_forestDegrees,List.append_nil] using hh

def incrementWord (l : List ℕ) : List ℤ := l.map (fun k : ℕ => (k:ℤ)-1)

def SuffixNegative (l : List ℕ) : Prop := ∀ j<l.length,(incrementWord (l.drop j)).sum<0

lemma suffixNegative_tail {k : ℕ} {l : List ℕ} (h : SuffixNegative (k::l)) : SuffixNegative l := by
  intro j hj
  simpa only [List.drop_succ_cons] using h (j+1) (by simpa using hj)

lemma build_correct {l : List ℕ} (h : SuffixNegative l) :
    forestDegrees (build l [])=l ∧ ((build l []).length:ℤ)= -(incrementWord l).sum := by
  induction l with
  | nil => simp [build,forestDegrees,incrementWord]
  | cons k l ih =>
    obtain ⟨he,hlen⟩ := ih (suffixNegative_tail h)
    have hneg := h 0 (by simp)
    simp only [List.drop_zero,incrementWord,List.map_cons,List.sum_cons] at hneg
    have hk : k≤(build l []).length := by
      change ((build l []).length:ℤ)= -(incrementWord l).sum at hlen
      unfold incrementWord at hlen
      omega
    constructor
    · simp only [build, forestDegrees, List.flatMap_cons, degrees, List.cons_append]
      change ((List.take k (build l [])).length)::
        (forestDegrees (List.take k (build l []))++forestDegrees (List.drop k (build l [])))=k::l
      rw [List.length_take,Nat.min_eq_left hk]
      rw [forestDegrees, forestDegrees, ← List.flatMap_append, List.take_append_drop]
      exact congrArg (List.cons k) he
    · simp only [build,List.length_cons,List.length_drop,incrementWord,List.map_cons,List.sum_cons]
      rw [Nat.cast_add, Nat.cast_sub hk]
      simp only [Nat.cast_one]
      unfold incrementWord at hlen
      omega

lemma suffixNegative_of_excursion {l : List ℕ} (h : IsExcursionList (incrementWord l)) :
    SuffixNegative l := by
  intro j hj
  have hp := h.2 j (by simpa [incrementWord] using hj)
  have hh : (incrementWord (l.drop j)).sum=(incrementWord l).sum-prefixSum (incrementWord l) j := by
    rw [incrementWord,List.map_drop,sum_drop]
    rfl
  rw [hh,h.1]
  omega

lemma exists_tree_of_excursion {l : List ℕ} (h : IsExcursionList (incrementWord l)) :
    ∃ t : PlaneTree,t.degrees=l := by
  obtain ⟨he,hlen⟩ := build_correct (suffixNegative_of_excursion h)
  rw [h.1] at hlen
  have hlen' : (build l []).length=1 := by omega
  obtain ⟨t,ht⟩ := List.length_eq_one_iff.mp hlen'
  exact ⟨t,by simpa [ht,forestDegrees] using he⟩

/-- Reversal of all child orders, without imposing any symmetry on marks. -/
def mirror : PlaneTree → PlaneTree
  | node ts => node (ts.reverse.map mirror)

lemma mirror_mirror (t : PlaneTree) : t.mirror.mirror=t := by
  induction t using inductionMem with
  | hn ts ih =>
    simp only [mirror,List.map_reverse,List.reverse_reverse,List.map_map]
    congr 1
    apply Eq.trans ?_ (List.map_id' _)
    apply List.map_congr_left
    intro t ht
    exact ih t ht

lemma incrementWord_append (l l' : List ℕ) :
    incrementWord (l++l')=incrementWord l++incrementWord l' := by
  simp [incrementWord]

lemma suffixNegative_append {l l' : List ℕ} (h : SuffixNegative l)
    (h' : SuffixNegative l') (hs : (incrementWord l').sum≤0) : SuffixNegative (l++l') := by
  intro j hj
  by_cases hja : j<l.length
  · rw [List.drop_append_of_le_length (Nat.le_of_lt hja),incrementWord_append,List.sum_append]
    exact add_lt_of_lt_of_nonpos (h j hja) hs
  · rw [List.drop_append,List.drop_eq_nil_of_le (by omega : l.length≤j),List.nil_append]
    exact h' (j-l.length) (by simp only [List.length_append] at hj; omega)

lemma degrees_properties (t : PlaneTree) :
    (incrementWord t.degrees).sum= -1 ∧ SuffixNegative t.degrees := by
  induction t using inductionMem with
  | hn ts ih =>
    have hf : ∀ fs : List PlaneTree,
        (∀ f ∈ fs, (incrementWord f.degrees).sum= -1 ∧ SuffixNegative f.degrees) →
        (incrementWord (forestDegrees fs)).sum= -(fs.length:ℤ) ∧
          SuffixNegative (forestDegrees fs) := by
      intro fs hfs
      induction fs with
      | nil => simp [forestDegrees,incrementWord,SuffixNegative]
      | cons f fs ih' =>
        have hp := hfs f (by simp)
        obtain ⟨hs,hn⟩ := ih' (by intro f hf; exact hfs f (by simp [hf]))
        have he : forestDegrees (f::fs)=f.degrees++forestDegrees fs := by simp [forestDegrees]
        rw [he]
        constructor
        · rw [incrementWord_append,List.sum_append,hp.1,hs]
          simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
          omega
        · exact suffixNegative_append hp.2 hn (by rw [hs]; omega)
    obtain ⟨hs,hn⟩ := hf ts ih
    have hsum : (incrementWord (node ts).degrees).sum= -1 := by
      rw [degrees]
      change (incrementWord (ts.length::forestDegrees ts)).sum= -1
      simp only [incrementWord,List.map_cons,List.sum_cons]
      change (ts.length:ℤ)-1+(incrementWord (forestDegrees ts)).sum= -1
      rw [hs]; omega
    exact ⟨hsum,fun j hj => by
      cases j with
      | zero => simpa only [List.drop_zero,hsum] using (by norm_num : (-1:ℤ)<0)
      | succ j =>
        simpa only [degrees,List.drop_succ_cons,forestDegrees] using
          hn j (by simpa only [degrees,List.length_cons,Nat.succ_lt_succ_iff,forestDegrees] using hj)⟩

lemma degrees_excursion (t : PlaneTree) : IsExcursionList (incrementWord t.degrees) := by
  obtain ⟨hs,hn⟩ := degrees_properties t
  refine ⟨hs,fun j hj => ?_⟩
  have hneg := hn j (by simpa [incrementWord] using hj)
  have he : (incrementWord (t.degrees.drop j)).sum =
      (incrementWord t.degrees).sum-prefixSum (incrementWord t.degrees) j := by
    rw [incrementWord,List.map_drop,sum_drop]; rfl
  rw [he,hs] at hneg
  omega

lemma degrees_nonempty (t : PlaneTree) : t.degrees≠[] := by cases t; simp [degrees]

lemma mirror_degrees_perm (t : PlaneTree) : t.mirror.degrees.Perm t.degrees := by
  induction t using inductionMem with
  | hn ts ih =>
    simp only [mirror,degrees,List.length_map,List.length_reverse]
    apply List.Perm.cons
    rw [List.flatMap_map]
    exact (List.reverse_perm ts).flatMap (fun t ht => ih t (by simpa using ht))

lemma mirror_size (t : PlaneTree) : t.mirror.degrees.length=t.degrees.length :=
  t.mirror_degrees_perm.length_eq

lemma mirror_weight (w : ℕ → ℝ) (t : PlaneTree) :
    (t.mirror.degrees.map w).prod=(t.degrees.map w).prod :=
  (t.mirror_degrees_perm.map w).prod_eq

end PlaneTree
end FKCRT.TreeCoding
end


noncomputable section
open List
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable

abbrev CoreLabel := Option Core
namespace CoreLabel

def arity : CoreLabel → ℕ
  | none => 0
  | some c => c.val.length

end CoreLabel

namespace CoreTree

def labels : CoreTree → List CoreLabel
  | leaf => [none]
  | branch c ts => some c::(List.ofFn (fun i => labels (ts i))).flatten

lemma labels_branch (c : Core) (ts : Fin c.val.length → CoreTree) :
    (branch c ts).labels=some c::(List.ofFn ts).flatMap labels := by
  simp [labels,List.flatMap_def,Function.comp_def]

def degrees (t : CoreTree) : List ℕ := t.labels.map CoreLabel.arity

def assemble (c : CoreLabel) (fs : List CoreTree) : CoreTree :=
  match c with
  | none => leaf
  | some c => branch c (fun i => fs[i.val]?.getD leaf)

def build : List CoreLabel → List CoreTree → List CoreTree
  | [],fs => fs
  | c::l,fs => let ts := build l fs; assemble c ts::ts.drop c.arity

lemma build_append (l l' : List CoreLabel) (fs : List CoreTree) :
    build (l++l') fs=build l (build l' fs) := by
  induction l with
  | nil => rfl
  | cons c l ih => simp only [List.cons_append,build,ih]

lemma build_labels (T : CoreTree) (fs : List CoreTree) : build T.labels fs=T::fs := by
  induction T generalizing fs with
  | leaf => simp [labels,build,assemble,CoreLabel.arity]
  | branch c ts ih =>
    have hf : ∀ (xs : List CoreTree), (∀ t∈xs,∀ fs,build t.labels fs=t::fs)  → 
        ∀ fs,build (xs.flatMap labels) fs=xs++fs := by
      intro xs hx fs
      induction xs with
      | nil => rfl
      | cons t xs ih' =>
        rw [List.flatMap_cons,build_append,ih' (by aesop),hx t (by simp)]
        rfl
    have he := hf (List.ofFn ts) (by
      intro t ht
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht
      exact ih i) fs
    rw [labels_branch,build,he]
    simp only [CoreLabel.arity,assemble]
    have ha : (fun i : Fin c.val.length => ((List.ofFn ts)++fs)[i.val]?.getD leaf)=ts := by
      funext i
      rw [List.getElem?_append_left (by simp),List.getElem?_eq_getElem (by simp)]
      simp
    rw [ha]
    simp

lemma labels_injective : Function.Injective labels := by
  intro T U h
  have hh := congrArg (fun l => build l []) h
  simpa only [build_labels,List.cons.injEq,and_true] using hh

lemma ofFn_getD_eq_take (fs : List CoreTree) {k : ℕ} (hk : k≤fs.length) :
    List.ofFn (fun i : Fin k => fs[i.val]?.getD leaf)=fs.take k := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left hk]
  · intro i h1 h2
    have hi : i<k := by simpa using h1
    rw [List.getElem_ofFn,List.getElem_take]
    rw [List.getElem?_eq_getElem (hi.trans_le hk)]
    rfl

lemma assemble_labels (c : CoreLabel) (fs : List CoreTree) (hc : c.arity≤fs.length) :
    (assemble c fs).labels=c::(fs.take c.arity).flatMap labels := by
  cases c with
  | none => simp [assemble,labels,CoreLabel.arity]
  | some c =>
    simp only [assemble,labels_branch,CoreLabel.arity]
    exact congrArg (fun xs : List CoreTree => some c::xs.flatMap labels)
      (ofFn_getD_eq_take fs (k := c.val.length) hc)

lemma build_correct {l : List CoreLabel}
    (h : FKCRT.TreeCoding.PlaneTree.SuffixNegative (l.map CoreLabel.arity)) :
    (build l []).flatMap labels=l ∧
      ((build l []).length:ℤ)= -(FKCRT.TreeCoding.PlaneTree.incrementWord (l.map CoreLabel.arity)).sum := by
  induction l with
  | nil => simp [build,FKCRT.TreeCoding.PlaneTree.incrementWord]
  | cons c l ih =>
    obtain ⟨he,hlen⟩ := ih (FKCRT.TreeCoding.PlaneTree.suffixNegative_tail h)
    have hneg := h 0 (by simp)
    simp only [List.map_cons,List.drop_zero,FKCRT.TreeCoding.PlaneTree.incrementWord,List.sum_cons] at hneg
    have hk : c.arity≤(build l []).length := by
      unfold FKCRT.TreeCoding.PlaneTree.incrementWord at hlen
      omega
    constructor
    · simp only [build,List.flatMap_cons,assemble_labels c _ hk,List.cons_append]
      rw [← List.flatMap_append,List.take_append_drop,he]
    · simp only [build,List.length_cons,List.length_drop,List.map_cons,
        FKCRT.TreeCoding.PlaneTree.incrementWord,List.sum_cons]
      rw [Nat.cast_add,Nat.cast_sub hk]
      simp only [Nat.cast_one]
      unfold FKCRT.TreeCoding.PlaneTree.incrementWord at hlen
      omega

/-- The actual labelled arity excursion determines exactly one connected-core
ordered tree. No probabilistic independence is part of this statement. -/
theorem exists_of_excursion {l : List CoreLabel}
    (h : FKCRT.TreeCoding.IsExcursionList
      (FKCRT.TreeCoding.PlaneTree.incrementWord (l.map CoreLabel.arity))) :
    ∃ T : CoreTree,T.labels=l := by
  obtain ⟨he,hlen⟩ := build_correct (FKCRT.TreeCoding.PlaneTree.suffixNegative_of_excursion h)
  rw [h.1] at hlen
  have hl : (build l []).length=1 := by omega
  obtain ⟨T,hT⟩ := List.length_eq_one_iff.mp hl
  exact ⟨T,by simpa [hT] using he⟩

end CoreTree
end FKCRT.Inventory
end

end OAI
