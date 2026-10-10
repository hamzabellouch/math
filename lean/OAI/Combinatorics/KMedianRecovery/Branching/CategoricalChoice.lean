import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.FilterItem
import OAI.Combinatorics.KMedianRecovery.Encoding.RationalBest
import OAI.Combinatorics.KMedianRecovery.Branching.CategoricalScore

namespace OAI

namespace MetricKMedianRecovery.OrderedMaximum
lemma cast_ofList {E : Type*} (score : E→ℚ) (as : List E) (h : as≠[]) :
    ofList (fun a=>(score a:ℝ)) as h=ofList score as h := cast_run score (as.head h) as.tail
end MetricKMedianRecovery.OrderedMaximum
namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {q a T L : ℕ}
def elements (q : ℕ) : List (Fin q) := List.ofFn id
lemma mem_elements (e : Fin q) : e∈elements q := by simp [elements]
noncomputable def rule (part : Fin q→Fin a) (hp : Function.Surjective part) : Categorical.Selected.Rule part :=
  Categorical.Selected.orderedRule (elements q) mem_elements part hp
noncomputable def bagTest (x : List Bool) : Bool :=
  decide (value (elementPart (pairBits (extractPrefix (extractPrefix x),discardPrefix x)))=
    value (discardPrefix (extractPrefix x)))
noncomputable def bagTest_computes : PolyComputes (fun x=>[bagTest x]) :=
  NatOps.eq ((((extractPrefix_computes.comp extractPrefix_computes).pair discardPrefix_computes).comp elementPart_computes))
    (extractPrefix_computes.comp discardPrefix_computes)
noncomputable def bagWords (x : List Bool) : List Bool :=
  filterWith bagTest (pairBits (x,Indices.run (field 3 (extractPrefix x))))
noncomputable def bagWords_computes : PolyComputes bagWords :=
  (id_computes.pair ((extractPrefix_computes.comp (field_computes 3)).comp Indices.run_computes)).comp
    (filterWith_computes bagTest_computes)
lemma bagTest_pack (ctx : List Bool) (part : Fin q→Fin a) (r : Fin a→Fin T→Option (Fin q))
    (seed : Categorical.OracleSeed (Fin q) a T L) (j : Fin a) (e : Fin q) :
    bagTest (pairBits (pairBits (scorePack ctx part r seed,j.val.bits),elemBits e))=decide (part e=j) := by
  simp only [bagTest,extractPrefix_pairBits,discardPrefix_pairBits,elementPart_pack,value_bits]
  exact decide_eq_decide.mpr ⟨Fin.ext,fun h=>congrArg Fin.val h⟩
lemma bagWords_pack (ctx : List Bool) (part : Fin q→Fin a) (r : Fin a→Fin T→Option (Fin q))
    (seed : Categorical.OracleSeed (Fin q) a T L) (j : Fin a) :
    bagWords (pairBits (scorePack ctx part r seed,j.val.bits))=
      encode ((Categorical.Selected.bag (elements q) part j).map elemBits) := by
  unfold bagWords
  have hfield : field 3 (extractPrefix (pairBits (scorePack ctx part r seed,j.val.bits)))=partBits part := by
    simp only [extractPrefix_pairBits,scorePack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
      Option.getD_some]
  rw [hfield]
  simp only [partBits,indices_ofFn]
  rw [show List.ofFn (fun i : Fin q=>i.val.bits)=(elements q).map elemBits by
    simp only [elements,List.map_ofFn,Function.comp_def,elemBits,id_eq]]
  rw [filterWith_encode,List.filter_map]
  simp only [Function.comp_def,bagTest_pack,Categorical.Selected.bag]
noncomputable def choose (g : List Bool→List Bool) (x : List Bool) : List Bool :=
  BinaryRationalBest.fromList (score g) (pairBits (extractPrefix x,bagWords x))
noncomputable def choose_computes {g : List Bool→List Bool} (hg : PolyComputes g) : PolyComputes (choose g) :=
  (extractPrefix_computes.pair bagWords_computes).comp (BinaryRationalBest.fromList_computes (score_computes hg))
lemma choose_pack (g : List Bool→List Bool) (ctx : List Bool) (G : Finset (Fin q)→ℚ)
    (hg : ∀ xs : List (Fin q),g (pairBits (ctx,encode (xs.map elemBits)))=BinaryRational.encode (G xs.toFinset))
    (part : Fin q→Fin a) (hp : Function.Surjective part) (r : Fin a→Fin T→Option (Fin q))
    (seed : Categorical.OracleSeed (Fin q) a T L) (j : Fin a) :
    choose g (pairBits (scorePack ctx part r seed,j.val.bits))=
      elemBits ((rule part hp).choose (Categorical.scores part (fun S=>(G S:ℝ)) r seed) j) := by
  simp only [choose,extractPrefix_pairBits,bagWords_pack]
  rw [BinaryRationalBest.fromList_pack elemBits (score g) (scorePack ctx part r seed)
    (rationalScore G part r seed) (fun e=>score_pack g ctx G hg part r seed e)
    _ (Categorical.Selected.bag_ne_nil (elements q) mem_elements part hp j)]
  simp only [rule,Categorical.Selected.orderedRule]
  rw [show Categorical.scores part (fun S=>(G S:ℝ)) r seed=(fun e=>(rationalScore G part r seed e:ℝ)) from
    funext (fun e=>(rationalScore_cast G part r seed e).symm),OrderedMaximum.cast_ofList]
noncomputable def choices (g : List Bool→List Bool) (x : List Bool) : List Bool :=
  mapWith (choose g) (pairBits (x,Indices.run (field 1 x)))
attribute [local irreducible] mapWith
noncomputable def choices_computes {g : List Bool→List Bool} (hg : PolyComputes g) : PolyComputes (choices g) := by
  unfold choices
  exact (id_computes.pair ((field_computes 1).comp Indices.run_computes)).comp (mapWith_computes (choose_computes hg))
lemma choices_pack (g : List Bool→List Bool) (ctx : List Bool) (G : Finset (Fin q)→ℚ)
    (hg : ∀ xs : List (Fin q),g (pairBits (ctx,encode (xs.map elemBits)))=BinaryRational.encode (G xs.toFinset))
    (part : Fin q→Fin a) (hp : Function.Surjective part) (r : Fin a→Fin T→Option (Fin q))
    (seed : Categorical.OracleSeed (Fin q) a T L) :
    choices g (scorePack ctx part r seed)=choicesBits elemBits
      ((rule part hp).choose (Categorical.scores part (fun S=>(G S:ℝ)) r seed)) := by
  unfold choices
  simp only [scorePack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    tableBits,indices_ofFn,mapWith_ofFn]
  change encode (List.ofFn (fun j=>choose g (pairBits (scorePack ctx part r seed,j.val.bits))))=_
  simp only [choose_pack g ctx G hg part hp,choicesBits]
end MetricKMedianRecovery.BitMachine.BinaryCategorical

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {q a T L : ℕ}
def stepContext (ctx : List Bool) (part : Fin q→Fin a) (T : ℕ) : List Bool :=
  encode [ctx,partBits part,List.replicate T true]
def stateBits (s : Categorical.GreedyState (Fin q) a T) : List Bool := encode [s.1.bits,tableBits elemBits s.2]
noncomputable def stepScore (x : List Bool) : List Bool :=
  encode [field 0 (Find.context x),field 1 (Fold.accum x),Find.item x,field 1 (Find.context x)]
noncomputable def stepScore_computes : PolyComputes stepScore :=
  cons_computes (Find.context_computes.comp (field_computes 0))
    (cons_computes (Fold.accum_computes.comp (field_computes 1))
      (cons_computes Find.item_computes (cons_computes (Find.context_computes.comp (field_computes 1)) (const_computes []))))
noncomputable def nextTable (g : List Bool→List Bool) (x : List Bool) : List Bool :=
  advance (encode [field 1 (Fold.accum x),choices g (stepScore x),field 0 (Fold.accum x)])
attribute [local irreducible] advance choices
noncomputable def nextTable_computes {g : List Bool→List Bool} (hg : PolyComputes g) : PolyComputes (nextTable g) := by
  unfold nextTable
  exact (cons_computes (Fold.accum_computes.comp (field_computes 1))
    (cons_computes (stepScore_computes.comp (choices_computes hg))
      (cons_computes (Fold.accum_computes.comp (field_computes 0)) (const_computes [])))).comp advance_computes
noncomputable def step (g : List Bool→List Bool) (x : List Bool) : List Bool :=
  if value (field 0 (Fold.accum x))<(field 2 (Find.context x)).length then
    encode [(value (field 0 (Fold.accum x))+1).bits,nextTable g x]
  else Fold.accum x
noncomputable def step_computes {g : List Bool→List Bool} (hg : PolyComputes g) : PolyComputes (step g) := by
  have hn := NatOps.add (Fold.accum_computes.comp (field_computes 0)) (const_computes (1:ℕ).bits)
  have hu := cons_computes hn (cons_computes (nextTable_computes hg) (const_computes []))
  have he := (NatOps.lt (Fold.accum_computes.comp (field_computes 0))
    ((Find.context_computes.comp (field_computes 2)).comp UnaryResources.lengthBits_computes)).cond hu Fold.accum_computes
  unfold step
  simpa only [Function.comp_def,value_bits,UnaryResources.lengthBits_eq,decide_eq_true_eq,encode] using he
lemma stepScore_pack (ctx : List Bool) (part : Fin q→Fin a) (s : Categorical.GreedyState (Fin q) a T)
    (seed : Categorical.OracleSeed (Fin q) a T L) :
    stepScore (pairBits (stepContext ctx part T,pairBits (oracleBits seed,stateBits s)))=scorePack ctx part s.2 seed := by
  simp only [stepScore,stepContext,stateBits,Find.context,Find.item,Fold.accum,Function.comp_apply,
    extractPrefix_pairBits,discardPrefix_pairBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,scorePack]
lemma nextTable_pack (g : List Bool→List Bool) (ctx : List Bool) (G : Finset (Fin q)→ℚ)
    (hg : ∀ xs : List (Fin q),g (pairBits (ctx,encode (xs.map elemBits)))=BinaryRational.encode (G xs.toFinset))
    (part : Fin q→Fin a) (hp : Function.Surjective part) (s : Categorical.GreedyState (Fin q) a T)
    (ht : s.1<T) (seed : Categorical.OracleSeed (Fin q) a T L) :
    nextTable g (pairBits (stepContext ctx part T,pairBits (oracleBits seed,stateBits s)))=
      tableBits elemBits (Categorical.advance s.2 ⟨s.1,ht⟩
        ((rule part hp).choose (Categorical.scores part (fun S=>(G S:ℝ)) s.2 seed))) := by
  unfold nextTable
  rw [stepScore_pack,choices_pack g ctx G hg part hp]
  simp only [Fold.accum,discardPrefix_pairBits,stateBits,
    field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  exact advance_pack elemBits s.2 ⟨s.1,ht⟩ _
lemma step_pack (g : List Bool→List Bool) (ctx : List Bool) (G : Finset (Fin q)→ℚ)
    (hg : ∀ xs : List (Fin q),g (pairBits (ctx,encode (xs.map elemBits)))=BinaryRational.encode (G xs.toFinset))
    (part : Fin q→Fin a) (hp : Function.Surjective part) (s : Categorical.GreedyState (Fin q) a T)
    (seed : Categorical.OracleSeed (Fin q) a T L) :
    step g (pairBits (stepContext ctx part T,pairBits (oracleBits seed,stateBits s)))=
      stateBits (Categorical.Selected.greedyStep part (rule part hp) (fun S=>(G S:ℝ)) s seed) := by
  unfold step
  have hc : value (field 0 (Fold.accum (pairBits (stepContext ctx part T,pairBits (oracleBits seed,stateBits s)))))=s.1 := by
    simp only [Fold.accum,discardPrefix_pairBits,stateBits,
      field_encode,List.getElem?_cons_zero,Option.getD_some,value_bits]
  have hT : (field 2 (Find.context (pairBits (stepContext ctx part T,pairBits (oracleBits seed,stateBits s))))).length=T := by
    simp only [Find.context,extractPrefix_pairBits,stepContext,field_encode,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some,List.length_replicate]
  rw [hc,hT]
  by_cases ht : s.1<T
  · rw [ite_eq_left ht,nextTable_pack g ctx G hg part hp s ht]
    simp only [Categorical.Selected.greedyStep,dite_eq_left ht,stateBits]
  · simp only [ite_eq_right ht,Categorical.Selected.greedyStep,dite_eq_right ht,Fold.accum,discardPrefix_pairBits]
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
