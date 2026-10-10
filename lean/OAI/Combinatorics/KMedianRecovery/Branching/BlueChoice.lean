import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Basic
import OAI.Combinatorics.KMedianRecovery.Machines.CappedFold

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {A : Type*}
abbrev Candidate (A : Type*) := Option (ℚ×A)
def value : Candidate A→WithTop ℝ
  | none=>⊤
  | some (q,_)=>((q:ℝ):WithTop ℝ)
def choose : Candidate A→Candidate A→Candidate A
  | none,y=>y
  | x,none=>x
  | some x,some y=>if x.1≤y.1 then some x else some y
lemma value_choose (x y : Candidate A) : value (choose x y)=min (value x) (value y) := by
  cases x with
  | none=>simp [choose,value]
  | some x=>
    cases y with
    | none=>simp [choose,value]
    | some y=>
      dsimp [choose,value]
      split_ifs with h
      · apply (min_eq_left ?_).symm
        exact WithTop.coe_le_coe.mpr (by exact_mod_cast h)
      · apply (min_eq_right ?_).symm
        exact WithTop.coe_le_coe.mpr (by exact_mod_cast (le_of_not_ge h))
lemma choose_mem (x y : Candidate A) : choose x y=x ∨ choose x y=y := by
  cases x <;> cases y <;> simp only [choose]
  all_goals first | exact Or.inl trivial | exact Or.inr trivial | (split_ifs <;> simp)
lemma choose_property (P : Candidate A→Prop) (x y : Candidate A) (hx : P x) (hy : P y) : P (choose x y) := by
  rcases choose_mem x y with h|h
  · rw [h];exact hx
  · rw [h];exact hy

def select (xs : List (Candidate A)) : Candidate A := xs.foldl choose none
lemma fold_property (P : Candidate A→Prop) (xs : List (Candidate A)) (s : Candidate A)
    (hs : P s) (hx : ∀ x∈xs,P x) : P (xs.foldl choose s) := by
  induction xs generalizing s with
  | nil=>exact hs
  | cons x xs ih=>exact ih (choose s x) (choose_property P s x hs (hx x (by simp))) (fun x h=>hx x (by simp [h]))
lemma fold_value (xs : List (Candidate A)) (s : Candidate A) :
    value (xs.foldl choose s)=min (value s) ((xs.map value).foldr min ⊤) := by
  induction xs generalizing s with
  | nil=>simp
  | cons x xs ih=>simp only [List.foldl_cons,ih,value_choose,List.map_cons,List.foldr_cons,min_assoc]
lemma select_value (xs : List (Candidate A)) : value (select xs)=((xs.map value).foldr min ⊤) := by
  unfold select
  rw [fold_value]
  change min ⊤ _=_
  exact min_top_left _
lemma fold_mem (xs : List (Candidate A)) (s : Candidate A) : xs.foldl choose s=s ∨ xs.foldl choose s∈xs := by
  induction xs generalizing s with
  | nil=>simp
  | cons x xs ih=>
    rw [List.foldl_cons]
    rcases ih (choose s x) with h|h
    · rcases choose_mem s x with he|he
      · exact Or.inl (h.trans he)
      · exact Or.inr (List.mem_cons.mpr (Or.inl (h.trans he)))
    · exact Or.inr (List.mem_cons_of_mem _ h)
end MetricKMedianRecovery.BlueDP
namespace MetricKMedianRecovery.BitMachine.BinaryBlueChoice
open WordOperations WordList BinaryArithmetic
variable {A : Type*}
def encode (enc : A→List Bool) : BlueDP.Candidate A→List Bool
  | none=>[]
  | some (q,a)=>WordList.encode [pairBits (BinaryRational.encode q,enc a)]
noncomputable def score (x : List Bool) : List Bool := extractPrefix (head x)
noncomputable def score_computes : PolyComputes score := WordList.head_computes.comp extractPrefix_computes
noncomputable def run (x : List Bool) : List Bool :=
  if extractPrefix x=[] then discardPrefix x else
  if discardPrefix x=[] then extractPrefix x else
  if BinaryRational.decode (score (extractPrefix x))≤BinaryRational.decode (score (discardPrefix x))
    then extractPrefix x else discardPrefix x
noncomputable def run_computes : PolyComputes run := by
  unfold run
  simpa only [Function.comp_def,decide_eq_true_eq] using
   (extractPrefix_computes.comp isEmpty_computes).cond discardPrefix_computes
    ((discardPrefix_computes.comp isEmpty_computes).cond extractPrefix_computes
      ((RatOps.le (RatOps.ofWords (extractPrefix_computes.comp score_computes))
        (RatOps.ofWords (discardPrefix_computes.comp score_computes))).cond extractPrefix_computes discardPrefix_computes))
lemma run_pack (enc : A→List Bool) (x y : BlueDP.Candidate A) :
    run (pairBits (encode enc x,encode enc y))=encode enc (BlueDP.choose x y) := by
  rw [run,extractPrefix_pairBits,discardPrefix_pairBits]
  cases x with
  | none=>rw [show encode enc none=[] from rfl,ite_eq_left rfl];rfl
  | some x=>
    cases x with
    | mk q a=>
      have hx : encode enc (some (q,a))≠[] := by simp [encode,WordList.encode,WordList.cons,pairBits]
      rw [ite_eq_right hx]
      cases y with
      | none=>rw [show encode enc none=[] from rfl,ite_eq_left rfl];rfl
      | some y=>
        cases y with
        | mk r b=>
          have hy : encode enc (some (r,b))≠[] := by simp [encode,WordList.encode,WordList.cons,pairBits]
          rw [ite_eq_right hy]
          simp only [score,encode,WordList.encode,head_cons,extractPrefix_pairBits,BinaryRational.decode_encode,BlueDP.choose]
          split_ifs <;> rfl

noncomputable def step (x : List Bool) : List Bool := run (pairBits (Fold.accum x,Find.item x))
noncomputable def step_computes : PolyComputes step := (Fold.accum_computes.pair Find.item_computes).comp run_computes
noncomputable def select (x : List Bool) : List Bool := CappedFold.run step (pairBits (x,Fold.pack x [] []))
noncomputable def select_computes : PolyComputes select :=
  (id_computes.pair (Fold.pack_computes id_computes (const_computes []) (const_computes []))).comp (CappedFold.run_computes step_computes)
lemma select_pack (enc : A→List Bool) (xs : List (BlueDP.Candidate A)) :
    select (WordList.encode (xs.map (encode enc)))=encode enc (BlueDP.select xs) := by
  rw [select]
  change CappedFold.run step (pairBits (WordList.encode (xs.map (encode enc)),
    Fold.pack (WordList.encode (xs.map (encode enc))) [] (encode enc none)))=_
  apply CappedFold.run_typed (encode enc) (encode enc) BlueDP.choose step [] _ (s:=none) (xs:=xs)
  · intro s a
    simp only [step,Fold.accum,Find.item,Function.comp_apply,discardPrefix_pairBits,extractPrefix_pairBits,run_pack]
  · intro n
    rcases BlueDP.fold_mem (xs.take n) (none : BlueDP.Candidate A) with he|he
    · rw [he];simp [encode]
    · exact length_member_le_encode (List.mem_map.mpr ⟨_,List.mem_of_mem_take he,rfl⟩)

end MetricKMedianRecovery.BitMachine.BinaryBlueChoice

end OAI
