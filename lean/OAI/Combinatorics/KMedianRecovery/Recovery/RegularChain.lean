import Mathlib
import OAI.Combinatorics.KMedianRecovery.Machines.MatchSize
import OAI.Combinatorics.KMedianRecovery.Machines.RefineMachine

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRegularChain
open WordOperations WordList RationalLeaves CanonicalMergePath PhaseSequence
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryRegular.run BinaryRefine.run
noncomputable def regularInput (x : List Bool) : List Bool := encode [field 0 x,field 1 x,field 5 x,field 4 x]
noncomputable def regularInput_computes : PolyComputes regularInput := list_computes [field 0,field 1,field 5,field 4] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl <;> exact ⟨field_computes _⟩)
noncomputable def context (x : List Bool) : List Bool := encode [field 2 (field 0 x),field 3 x,field 1 x,field 2 x]
noncomputable def context_computes : PolyComputes context :=
  list_computes [field 2 ∘ field 0,field 3,field 1,field 2] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl
    · exact ⟨(field_computes 0).comp (field_computes 2)⟩
    · exact ⟨field_computes _⟩
    · exact ⟨field_computes _⟩
    · exact ⟨field_computes _⟩)
noncomputable def vertices (x : List Bool) : List Bool := cons (field 4 x) (BinaryRegular.run (regularInput x))
noncomputable def vertices_computes : PolyComputes vertices :=
  cons_computes (field_computes 4) (regularInput_computes.comp BinaryRegular.run_computes)
noncomputable def run (x : List Bool) : List Bool := BinaryRefine.run (pairBits (context x,vertices x))
noncomputable def run_computes : PolyComputes run := (context_computes.pair vertices_computes).comp BinaryRefine.run_computes
def pack {m : ℕ} (base : List Bool) (key spare : ℕ) (R H G : List (Label (Fin m))) : List Bool :=
  encode [base,key.bits,spare.bits,labels R,labels H,labels G]
lemma regularInput_pack {m : ℕ} (base : List Bool) (key spare : ℕ) (R H G : List (Label (Fin m))) :
    regularInput (pack base key spare R H G)=BinaryRegular.pack base key G H := by
  simp only [regularInput,pack,BinaryRegular.pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
lemma context_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (key spare : ℕ) (R H G : List (Label (Fin m))) :
    context (pack (BinaryFiniteContext.pack distance loc F Q v z lam) key spare R H G)=BinaryRefine.ctxBits F R key spare := by
  simp only [context,pack,BinaryRefine.ctxBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryRegular.base_F]
lemma run_pack {m d : ℕ} [PseudoMetricSpace (Label (Fin m))]
    (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F B Q : Finset (Label (Fin m))) (v z lam : ℚ) (eta : ℝ) (key spare : ℕ) (R : List (Label (Fin m)))
    (hc : CorrectCompletion loc F (v:ℝ) z lam (FiniteLabelContinuation.complete loc (rows distance) F v z lam))
    (hv : (0:ℝ)<v) (hvsmall : (v:ℝ)<1/6) (hz : (0:ℝ)<z) (hlam : (0:ℝ)<lam) (heta : 0≤eta)
    (hQ : Q⊆F∪B) (hdis : Disjoint F B)
    (hrow : ∀ i∈F,bidRow loc (1-3*(v:ℝ)) z Q i≤lam)
    (hfresh : ∀ i∈F,copy key i∉F∪B) (hco : ∀ i∈F,∀ j,dist (loc j) i=dist (loc j) (copy key i))
    (H G : List (Label (Fin m))) (hHr : ∀ i∈H,i∈F) (hGr : ∀ i∈G,i∈F)
    (hH : Valid loc F B Q v z lam eta H) (hG : Valid loc F B Q v z lam eta G) :
    run (pack (BinaryFiniteContext.pack distance loc F Q v z lam) key spare R H G)=
      historyBits (CanonicalMergeRefinement.regularChain F R
        (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q (copy key) (copy spare) H G) := by
  rw [run,context_pack]
  unfold vertices
  rw [regularInput_pack,BinaryRegular.run_pack distance loc F B Q v z lam eta key hc hv hvsmall hz hlam heta
    hQ hdis hrow hfresh hco G H hGr hHr hG hH]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  change BinaryRefine.run (pairBits (BinaryRefine.ctxBits F R key spare,
    historyBits (H::CanonicalMergePath.regularPath (FiniteLabelContinuation.complete loc (rows distance) F v z lam)
      Q (copy key) G H)))=_
  exact BinaryRefine.run_pack F R key spare H _
end MetricKMedianRecovery.BitMachine.BinaryRegularChain

namespace MetricKMedianRecovery.CanonicalMergeCrossing
variable {A B : Type*}
def walk (step : A → A → Option B) (finish : A → B) : A → List A → B
  | a,[]=>finish a
  | a,b::T=>match step a b with | some r=>r | none=>walk step finish b T

def slots (step : A → A → Option B) : A → List A → List (Option B)
  | _,[]=>[]
  | a,b::T=>step a b :: slots step b T

def firstPresent : List (Option B) → Option B
  | []=>none
  | none::T=>firstPresent T
  | some r::_=>some r

def finalNode : A → List A → A
  | a,[]=>a
  | _,b::T=>finalNode b T

lemma walk_slots (step : A → A → Option B) (finish : A → B) (a : A) (T : List A) :
    walk step finish a T=(firstPresent (slots step a T)).getD (finish (finalNode a T)) := by
  induction T generalizing a with
  | nil=>rfl
  | cons b T ih=>
    simp only [walk,slots,finalNode]
    cases step a b <;> simp only [firstPresent,Option.getD_some,ih]

lemma cuts_slots (step : A → A → Option B) (a : A) (T : List A) :
    (CanonicalMergeRefinement.cuts (a::T)).map
      (fun p=>match p.2.2 with | []=>none | b::_=>step p.2.1 b)=slots step a T++[none] := by
  induction T generalizing a with
  | nil=>rfl
  | cons b T ih=>
    rw [CanonicalMergeRefinement.cuts]
    simp only [List.map_cons,List.map_map,Function.comp_def]
    rw [ih]
    rfl
lemma firstPresent_append_none (L : List (Option B)) : firstPresent (L++[none])=firstPresent L := by
  induction L with
  | nil=>rfl
  | cons h L ih=>cases h <;> simp only [List.cons_append,firstPresent,ih]
lemma finalNode_reverse (a : A) (T : List A) : ((a::T).reverse.head?)=some (finalNode a T) := by
  induction T generalizing a with
  | nil=>rfl
  | cons b T ih=>
    rw [List.reverse_cons]
    change ((b::T).reverse++[a]).head?=some (finalNode b T)
    rw [List.head?_append]
    rw [ih]
    rfl

variable {X : Type*} [DecidableEq X]
def transition (F Q : Finset X) (k : ℕ) (P R : List X × List (List X)) : Option (Result X) :=
  if finalCount F Q R.1 R.2=k then some (.success R.1 R.2)
  else if PhaseCountCrossing.Sandwich k (finalCount F Q P.1 P.2) (finalCount F Q R.1 R.2) then
    some (edge F Q k P.1 R.1 P.2 R.2)
  else none
lemma scan_walk (F Q : Finset X) (k : ℕ) (complete : Finset X → List (List X)) (U : List (List X))
    (H : List X) (T : List (List X)) (S : List (List X)) :
    scan F Q k complete U H T S=walk (transition F Q k) (fun p=>.common p.1 p.2 U)
      (H,T) (S.map (fun J=>(J,complete (Q∪J.toFinset)))) := by
  induction S generalizing H T with
  | nil=>rfl
  | cons J S ih=>
    simp only [scan,List.map_cons,walk,transition]
    split_ifs <;> simp only [ih]
end MetricKMedianRecovery.CanonicalMergeCrossing

end OAI
