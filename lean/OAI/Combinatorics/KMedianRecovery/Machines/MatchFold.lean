import Mathlib
import OAI.Combinatorics.KMedianRecovery.Machines.DeleteSize
import OAI.Combinatorics.KMedianRecovery.Recovery.PathBounds

namespace OAI

namespace MetricKMedianRecovery.CanonicalMatch
open CanonicalMergePath PhaseSequence PhaseMergePath
variable {X D : Type*} [DecidableEq X]
structure Acc (X : Type*) where
  front : List X
  rest : List X
  vertices : List (List X)
  deriving DecidableEq

def step (complete : Finset X → List X) (Q : Finset X) (copy : X → X)
    (s : Acc X) (i : X) : Acc X :=
  let a:=advancePrefix complete Q copy s.front s.rest i
  ⟨s.front++[i],a.1,s.vertices++a.2⟩
lemma fold_result (complete : Finset X → List X) (Q : Finset X) (copy : X → X)
    (C U : List X) (V : List (List X)) (T : List X) :
    T.foldl (step complete Q copy) ⟨C,U,V⟩=
      ⟨C++T,(matchPrefix complete Q copy C U T).1,V++(matchPrefix complete Q copy C U T).2⟩ := by
  induction T generalizing C U V with
  | nil=>simp only [List.foldl_nil,List.append_nil,matchPrefix]
  | cons i T ih=>
    simp only [List.foldl_cons,step]
    rw [ih]
    simp only [matchPrefix,List.append_assoc,List.singleton_append]

variable [Fintype D] [PseudoMetricSpace X]
lemma fold_bounds (loc : D → X) (F B Q : Finset X) (copy : X → X)
    (v z lam eta : ℝ) (complete : Finset X → List X)
    (hc : CorrectCompletion loc F v z lam complete)
    (hv : 0<v) (hvsmall : v<1/6) (hz : 0<z) (hlam : 0<lam) (heta : 0≤eta)
    (hQ : Q⊆F∪B) (hdis : Disjoint F B)
    (hrow : ∀ k∈F,bidRow loc (1-3*v) z Q k≤lam)
    (hfresh : ∀ i∈F,copy i∉F∪B) (hco : ∀ i∈F,∀ j,dist (loc j) i=dist (loc j) (copy i))
    (C U T : List X) (hCr : ∀ i∈C,i∈F) (hUr : ∀ i∈U,i∈F) (hTr : ∀ i∈T,i∈F)
    (htarget : Prefix loc F B v z lam eta Q (C++T)) (hcur : Valid loc F B Q v z lam eta (C++U))
    {P : X → Prop} (hF : ∀ x∈F,P x) (hcopy : ∀ x∈F,P (copy x)) :
    let s:=T.foldl (step complete Q copy) ⟨C,U,[]⟩
    s.front.length≤F.card ∧ s.rest.length≤F.card ∧ s.vertices.length≤T.length*(F.card+2) ∧
    (∀ H∈s.vertices,H.length≤F.card+1) ∧
    (∀ x∈s.front,P x) ∧ (∀ x∈s.rest,P x) ∧ (∀ H∈s.vertices,∀ x∈H,P x) := by
  rw [fold_result,List.nil_append]
  dsimp only
  obtain ⟨hlen,hreg,hvalid,hpath⟩:=matchPrefix_spec loc F B Q copy v z lam eta complete hc
    hv hvsmall hz hlam heta hQ hdis hrow hfresh hco C U T hCr hUr hTr htarget hcur
  have hCT : ∀ x∈C++T,x∈F := fun x hx=>(List.mem_append.mp hx).elim (hCr x) (hTr x)
  have hbound:=regular_length hvalid.1 (fun x hx=>(List.mem_append.mp hx).elim (hCT x) (hreg x))
  simp only [List.length_append] at hbound
  refine ⟨by simp only [List.length_append]; omega,by omega,hlen,?_,?_,?_,?_⟩
  · exact fun H hH=>(hpath.vertices_good H hH).length_bound
  · exact fun x hx=>hF x (hCT x hx)
  · exact fun x hx=>hF x (hreg x hx)
  · exact hpath.vertices_mem hF hcopy (fun x hx=>hF x ((List.mem_append.mp hx).elim (hCr x) (hUr x)))
end MetricKMedianRecovery.CanonicalMatch

namespace MetricKMedianRecovery.BitMachine.BinaryMatch
open WordOperations WordList RationalLeaves CanonicalMatch
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)

def accBits {m : ℕ} (s : Acc (Label (Fin m))) : List Bool :=
  encode [labels s.front,labels s.rest,historyBits s.vertices]
def contextBits (base : List Bool) (key : ℕ) {m : ℕ} (F : Finset (Label (Fin m))) :=
  encode [base,key.bits,labels ((BinaryLabel.orderedSort F).map (copy key))]
def cf (n : ℕ) (x : List Bool) : List Bool := field n (extractPrefix x)
def sf (n : ℕ) (x : List Bool) : List Bool := field n (discardPrefix (discardPrefix x))
def item (x : List Bool) : List Bool := extractPrefix (discardPrefix x)
noncomputable def cf_computes (n : ℕ) : PolyComputes (cf n) := extractPrefix_computes.comp (field_computes n)
noncomputable def sf_computes (n : ℕ) : PolyComputes (sf n) :=
  (discardPrefix_computes.comp discardPrefix_computes).comp (field_computes n)
noncomputable def item_computes : PolyComputes item := discardPrefix_computes.comp extractPrefix_computes
noncomputable def copied (x : List Bool) : List Bool := BinaryLabel.copied (pairBits (cf 1 x,item x))
attribute [local irreducible] BinaryLabel.copied
noncomputable def copied_computes : PolyComputes copied :=
  ((cf_computes 1).pair item_computes).comp BinaryLabel.copied_computes
noncomputable def advancingInput (x : List Bool) : List Bool :=
  encode [cf 0 x,sf 0 x,sf 1 x,item x,copied x]
noncomputable def advancingInput_computes : PolyComputes advancingInput := list_computes
  [cf 0,sf 0,sf 1,item,copied] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl
    · exact ⟨cf_computes _⟩
    · exact ⟨sf_computes _⟩
    · exact ⟨sf_computes _⟩
    · exact ⟨item_computes⟩
    · exact ⟨copied_computes⟩)
noncomputable def advanced : List Bool → List Bool := BinaryAdvance.run ∘ advancingInput
noncomputable def advanced_computes : PolyComputes advanced := advancingInput_computes.comp BinaryAdvance.run_computes
attribute [local irreducible] advanced
noncomputable def front (x : List Bool) : List Bool := sf 0 x++WordList.cons (item x) []
noncomputable def prefix_computes : PolyComputes front :=
  (sf_computes 0).append (cons_computes item_computes (const_computes []))
noncomputable def rest : List Bool → List Bool := field 0 ∘ advanced
noncomputable def suffix_computes : PolyComputes rest := advanced_computes.comp (field_computes 0)
noncomputable def vertices (x : List Bool) : List Bool := sf 2 x++field 1 (advanced x)
noncomputable def vertices_computes : PolyComputes vertices :=
  (sf_computes 2).append (advanced_computes.comp (field_computes 1))
noncomputable def step (x : List Bool) : List Bool := encode [front x,rest x,vertices x]
noncomputable def step_computes : PolyComputes step := list_computes [front,rest,vertices] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl
  · exact ⟨prefix_computes⟩
  · exact ⟨suffix_computes⟩
  · exact ⟨vertices_computes⟩)

lemma advanced_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (key : ℕ)
    (s : Acc (Label (Fin m))) (a : Label (Fin m)) :
    advanced (pairBits (contextBits (BinaryFiniteContext.pack distance loc F Q v z lam) key F,
      pairBits (BinaryLabel.encode a,accBits s)))=
      encode [labels (CanonicalMergePath.advancePrefix
        (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q (copy key) s.front s.rest a).1,
        historyBits (CanonicalMergePath.advancePrefix
        (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q (copy key) s.front s.rest a).2] := by
  unfold advanced advancingInput copied cf sf item contextBits accBits
  simp only [Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryLabel.copied_pack]
  exact BinaryAdvance.run_pack distance loc F Q v z lam (copy key) s.front s.rest a
lemma step_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (key : ℕ)
    (s : Acc (Label (Fin m))) (a : Label (Fin m)) :
    step (pairBits (contextBits (BinaryFiniteContext.pack distance loc F Q v z lam) key F,
      pairBits (BinaryLabel.encode a,accBits s)))=
      accBits (CanonicalMatch.step (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q (copy key) s a) := by
  simp only [step,front,rest,vertices,Function.comp_apply,advanced_pack]
  simp only [sf,item,extractPrefix_pairBits,discardPrefix_pairBits,accBits,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  simp only [CanonicalMatch.step,BinaryFiniteContext.labels_append,BinaryFiniteContext.labels_cons,
    BinaryFiniteContext.labels_nil,BinaryFiniteMachine.historyBits_append]
end MetricKMedianRecovery.BitMachine.BinaryMatch

end OAI
