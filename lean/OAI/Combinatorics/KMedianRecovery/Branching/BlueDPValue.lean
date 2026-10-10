import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Blocks
import OAI.Combinatorics.KMedianRecovery.Branching.BlueChoice

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {A L : Type*}
def merge : Candidate (List A)→Candidate (List A)→Candidate (List A)
  | some (q,x),some (r,y)=>some (q+r,x++y)
  | _,_=>none
lemma value_merge (x y : Candidate (List A)) : value (merge x y)=value x+value y := by
  cases x with
  | none=>simp [merge,value]
  | some x=>
    cases y with
    | none=>simp [merge,value]
    | some y=>simp [merge,value,Rat.cast_add,WithTop.coe_add]
def collect (xs : List (Candidate (List A))) : Candidate (List A) := xs.foldr merge (some (0,[]))
lemma value_collect (xs : List (Candidate (List A))) : value (collect xs)=(xs.map value).sum := by
  induction xs with
  | nil=>simp [collect,value]
  | cons x xs ih=>simpa only [collect,List.foldr_cons,value_merge,List.map_cons,List.sum_cons] using congrArg (value x+·) ih
lemma collect_some (xs : List (Candidate (List A))) (q : ℚ) (w : List A) :
    collect xs=some (q,w) → ∀ x∈xs,x≠none := by
  induction xs generalizing q w with
  | nil=>simp
  | cons x xs ih=>
    intro he y hy
    rcases List.mem_cons.mp hy with rfl|hy
    · intro hx
      simp only [collect,List.foldr_cons,hx,merge] at he
      cases he
    · have ht : ∃ r z,collect xs=some (r,z) := by
        cases hx : x with
        | none=>simp only [collect,List.foldr_cons,hx,merge] at he;cases he
        | some x=>
          cases hz : collect xs with
          | none=>change merge _ (collect xs)=_ at he;rw [hz] at he;cases x;simp [merge] at he
          | some z=>exact ⟨z.1,z.2,rfl⟩
      obtain ⟨r,z,hz⟩:=ht
      exact ih r z hz y hy
lemma list_min_inf [DecidableEq L] (xs : List L) (f : L→WithTop ℝ) :
    ((xs.map f).foldr min ⊤)=xs.toFinset.inf f := by
  induction xs with
  | nil=>simp
  | cons x xs ih=>simp [ih]
lemma select_finset [DecidableEq L] (xs : List L) (f : L→Candidate A) :
    value (select (xs.map f))=xs.toFinset.inf (fun x=>value (f x)) := by
  rw [select_value,List.map_map]
  exact list_min_inf xs _

variable [LinearOrder L]
def enumBlocks (U : Finset L) : List (Finset L) :=
  (((U.sort (·≤·)).sublists).map List.toFinset).filter (·≠∅)
lemma enumBlocks_set (U : Finset L) : (enumBlocks U).toFinset=BlueSubsetDP.blocks U := by
  ext V
  simp only [enumBlocks,List.mem_toFinset,List.mem_filter,List.mem_map,List.mem_sublists,decide_eq_true_eq,BlueSubsetDP.mem_blocks]
  constructor
  · rintro ⟨⟨xs,hxs,rfl⟩,hx⟩
    refine ⟨Finset.nonempty_iff_ne_empty.mpr hx,?_⟩
    intro l hl
    exact (Finset.mem_sort (·≤·)).mp (hxs.subset (List.mem_toFinset.mp hl))
  · intro h
    refine ⟨⟨(U.sort (·≤·)).filter (fun l=>l∈V),List.filter_sublist,?_⟩,h.1.ne_empty⟩
    ext l
    simp only [List.mem_toFinset,List.mem_filter,Finset.mem_sort,decide_eq_true_eq]
    exact ⟨And.right,fun hv=>⟨h.2 hv,hv⟩⟩

def recurrence (C : Finset L→Candidate (List A)) : ℕ→Finset L→Candidate (List A)
  | 0,U=>if U=∅ then some (0,[]) else none
  | t+1,U=>select ((enumBlocks U).map (fun V=>merge (C V) (recurrence C t (U\V))))
lemma recurrence_value (C : Finset L→Candidate (List A)) (t : ℕ) (U : Finset L) :
    value (recurrence C t U)=BlueSubsetDP.value (fun V=>value (C V)) t U := by
  induction t generalizing U with
  | zero=>by_cases h : U=∅ <;> simp [recurrence,BlueSubsetDP.value,h,value]
  | succ t ih=>
    rw [recurrence,select_finset,enumBlocks_set]
    simp only [value_merge,ih,BlueSubsetDP.value]
def best (C : Finset L→Candidate (List A)) (c : ℕ) (U : Finset L) : Candidate (List A) :=
  if U=∅ then some (0,[]) else select ((List.range c).map (fun t=>recurrence C (t+1) U))
lemma range_succ_set (c : ℕ) : ((List.range c).map (·+1)).toFinset=Finset.Icc 1 c := by
  ext i
  simp only [List.mem_toFinset,List.mem_map,List.mem_range,Finset.mem_Icc]
  constructor
  · rintro ⟨j,hj,rfl⟩;omega
  · intro h;exact ⟨i-1,by omega,by omega⟩
lemma best_value (C : Finset L→Candidate (List A)) (c : ℕ) (U : Finset L) :
    value (best C c U)=BlueSubsetDP.best (fun V=>value (C V)) c U := by
  by_cases h : U=∅
  · simp [best,BlueSubsetDP.best,h,value]
  · rw [best,ite_eq_right h,BlueSubsetDP.best,ite_eq_right h]
    have he : ((List.range c).map (fun t=>recurrence C (t+1) U))=
      (((List.range c).map (·+1)).map (fun t=>recurrence C t U)) := by simp
    rw [he,select_finset,range_succ_set]
    simp only [recurrence_value]
end MetricKMedianRecovery.BlueDP

namespace MetricKMedianRecovery.BlueDP
variable {L R Y : Type*} [LinearOrder L] [LinearOrder R] [LinearOrder Y]
abbrev Atom (L R Y : Type*) := L×R×Y

def item (B : Finset R) (label : R→L) (q : R→Y→ℚ) (l : L) (y : Y) : Candidate (List (Atom L R Y)) :=
  select (((B.filter (label ·=l)).sort (·≤·)).map (fun r=>some (q r y,[(l,r,y)])))
def blockAt (B : Finset R) (label : R→L) (q : R→Y→ℚ) (U : Finset L) (y : Y) : Candidate (List (Atom L R Y)) :=
  collect ((U.sort (·≤·)).map (fun l=>item B label q l y))
def block (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (U : Finset L) : Candidate (List (Atom L R Y)) :=
  select ((F.sort (·≤·)).map (blockAt B label q U))
omit [LinearOrder Y] in
lemma item_value (B : Finset R) (label : R→L) (q : R→Y→ℚ) (l : L) (y : Y) :
    value (item B label q l y)=(B.filter (label ·=l)).inf (fun r=>((q r y:ℝ):WithTop ℝ)) := by
  rw [item,select_finset,Finset.sort_toFinset]
  rfl
omit [LinearOrder Y] in
lemma blockAt_value (B : Finset R) (label : R→L) (q : R→Y→ℚ) (U : Finset L) (y : Y) :
    value (blockAt B label q U y)=∑ l∈U,(B.filter (label ·=l)).inf (fun r=>((q r y:ℝ):WithTop ℝ)) := by
  rw [blockAt,value_collect,List.map_map]
  simp only [Function.comp_def,item_value]
  rw [←List.sum_toFinset _ (Finset.sort_nodup U (·≤·)),Finset.sort_toFinset]
lemma block_value (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (U : Finset L) :
    value (block B F label q U)=BlueSubsetDP.blockCost B F label (fun r y=>(q r y:ℝ)) U := by
  rw [block,select_finset,Finset.sort_toFinset]
  simp only [blockAt_value,BlueSubsetDP.blockCost]
lemma optimizer_value (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (c : ℕ) (U : Finset L) :
    value (best (block B F label q) c U)=BlueSubsetDP.best (BlueSubsetDP.blockCost B F label (fun r y=>(q r y:ℝ))) c U := by
  rw [best_value]
  simp only [block_value]
end MetricKMedianRecovery.BlueDP

end OAI
