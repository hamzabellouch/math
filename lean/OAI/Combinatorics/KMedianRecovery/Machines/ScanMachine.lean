import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.FirstPresent

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryScan
open WordOperations WordList RationalLeaves CanonicalMergeCrossing
open BinaryCross (ctxBits nodeBits resultBits)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryFiniteMachine.continuation BinaryNodeScan.run
noncomputable def cf (n : ℕ) : List Bool → List Bool := field n ∘ extractPrefix
noncomputable def cf_computes (n : ℕ) : PolyComputes (cf n) := extractPrefix_computes.comp (field_computes n)
noncomputable def opened (x : List Bool) : List Bool :=
  BinaryFiniteContext.union (pairBits (field 3 (cf 0 x),discardPrefix x))
noncomputable def opened_computes : PolyComputes opened :=
  ((cf_computes 0).comp (field_computes 3) |>.pair discardPrefix_computes).comp BinaryFiniteContext.union_computes
noncomputable def base (x : List Bool) : List Bool := BinaryFiniteContext.replaceOpen (pairBits (cf 0 x,opened x))
noncomputable def base_computes : PolyComputes base :=
  ((cf_computes 0).pair opened_computes).comp BinaryFiniteContext.replaceOpen_computes
noncomputable def contInput (x : List Bool) : List Bool := pairBits (cf 1 x,pairBits (cf 2 x,base x))
noncomputable def contInput_computes : PolyComputes contInput := (cf_computes 1).pair ((cf_computes 2).pair base_computes)
noncomputable def node (x : List Bool) : List Bool := pairBits (discardPrefix x,BinaryFiniteMachine.continuation (contInput x))
noncomputable def node_computes : PolyComputes node := discardPrefix_computes.pair (contInput_computes.comp BinaryFiniteMachine.continuation_computes)
def contCtx (base : List Bool) (n q : ℕ) : List Bool := encode [base,List.replicate n true,List.replicate q true]
lemma node_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (q n : ℕ) (H : List (Label (Fin m))) :
    node (pairBits (contCtx (BinaryFiniteContext.pack distance loc F Q v z lam) n q,labels H))=
      nodeBits (H,FiniteLabelContinuation.continuation loc (rows distance) F v lam q n (Q∪H.toFinset)) := by
  have ho : opened (pairBits (contCtx (BinaryFiniteContext.pack distance loc F Q v z lam) n q,labels H))=
      setBits (Q∪H.toFinset) := by
    simp only [opened,cf,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,contCtx,
      field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryFiniteContext.pack]
    exact BinaryFiniteContext.union_list_pack Q H
  simp only [node,contInput,base]
  rw [ho]
  simp only [cf,contCtx,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryFiniteContext.replaceOpen_pack,
    BinaryFiniteMachine.continuation_pack]
  rfl
noncomputable def mapCtx (x : List Bool) : List Bool := encode [field 0 x,field 1 x,field 2 x]
noncomputable def mapCtx_computes : PolyComputes mapCtx := list_computes [field 0,field 1,field 2] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl <;> exact ⟨field_computes _⟩)
noncomputable def nodes (x : List Bool) : List Bool :=
  cons (field 5 x) (mapWith node (pairBits (mapCtx x,field 6 x)))
noncomputable def nodes_computes : PolyComputes nodes := by
  have composeComputes (contextFunction nodeFunction : List Bool → List Bool)
      (contextComputes : PolyComputes contextFunction) (nodeComputes : PolyComputes nodeFunction) :
      PolyComputes (fun input=>cons (field 5 input)
        (mapWith nodeFunction (pairBits (contextFunction input,field 6 input)))) := by
    simpa only [Function.comp_def] using cons_computes (field_computes 5)
      ((contextComputes.pair (field_computes 6)).comp (mapWith_computes nodeComputes))
  exact composeComputes mapCtx node mapCtx_computes node_computes
noncomputable def scanInput (x : List Bool) : List Bool := encode [field 3 x,field 4 x,nodes x]
noncomputable def scanInput_computes : PolyComputes scanInput := list_computes [field 3,field 4,nodes] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl
  · exact ⟨field_computes _⟩
  · exact ⟨field_computes _⟩
  · exact ⟨nodes_computes⟩)
noncomputable def run : List Bool → List Bool := BinaryNodeScan.run ∘ scanInput
noncomputable def run_computes : PolyComputes run := scanInput_computes.comp BinaryNodeScan.run_computes
def pack {m : ℕ} (base : List Bool) (F Q : Finset (Label (Fin m))) (k n q : ℕ)
    (U : List (List (Label (Fin m)))) (H : List (Label (Fin m))) (T S : List (List (Label (Fin m)))) : List Bool :=
  encode [base,List.replicate n true,List.replicate q true,ctxBits F Q k,historyBits U,nodeBits (H,T),historyBits S]
lemma nodes_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (k n q : ℕ)
    (U : List (List (Label (Fin m)))) (H : List (Label (Fin m))) (T S : List (List (Label (Fin m)))) :
    nodes (pack (BinaryFiniteContext.pack distance loc F Q v z lam) F Q k n q U H T S)=
      encode (((H,T)::S.map (fun J=>(J,FiniteLabelContinuation.continuation loc (rows distance) F v lam q n
        (Q∪J.toFinset)))).map nodeBits) := by
  simp only [nodes,mapCtx,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  change cons (nodeBits (H,T)) (mapWith node (pairBits
    (contCtx (BinaryFiniteContext.pack distance loc F Q v z lam) n q,historyBits S)))=_
  simp only [historyBits,mapWith_encode,List.map_map,Function.comp_def,node_pack,List.map_cons]
  rfl
lemma run_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (k n q : ℕ)
    (U : List (List (Label (Fin m)))) (H : List (Label (Fin m))) (T S : List (List (Label (Fin m)))) :
    run (pack (BinaryFiniteContext.pack distance loc F Q v z lam) F Q k n q U H T S)=
      resultBits (scan F Q k (FiniteLabelContinuation.continuation loc (rows distance) F v lam q n) U H T S) := by
  simp only [run,Function.comp_apply,scanInput,nodes_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [scan_walk]
  exact BinaryNodeScan.run_pack F Q k U (H,T) _
end MetricKMedianRecovery.BitMachine.BinaryScan

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteCross
open WordOperations WordList RationalLeaves CanonicalMergePath PhaseSequence
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryRegularChain.run BinaryScan.run
noncomputable def chainInput (x : List Bool) : List Bool :=
  encode [field 0 x,field 1 x,field 2 x,field 2 (field 0 x),field 6 x,field 7 x]
noncomputable def chainInput_computes : PolyComputes chainInput :=
  list_computes [field 0,field 1,field 2,field 2 ∘ field 0,field 6,field 7] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨field_computes _⟩
    · exact ⟨field_computes _⟩
    · exact ⟨field_computes _⟩
    · exact ⟨(field_computes 0).comp (field_computes 2)⟩
    · exact ⟨field_computes _⟩
    · exact ⟨field_computes _⟩)
noncomputable def crossCtx (x : List Bool) : List Bool := encode [field 2 (field 0 x),field 3 (field 0 x),field 3 x]
noncomputable def crossCtx_computes : PolyComputes crossCtx :=
  list_computes [field 2 ∘ field 0,field 3 ∘ field 0,field 3] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl
    · exact ⟨(field_computes 0).comp (field_computes 2)⟩
    · exact ⟨(field_computes 0).comp (field_computes 3)⟩
    · exact ⟨field_computes _⟩)
noncomputable def nextQ (x : List Bool) : List Bool := true::field 5 x
noncomputable def nextQ_computes : PolyComputes nextQ := (const_computes [true]).append (field_computes 5)
noncomputable def firstNode (x : List Bool) : List Bool := pairBits (field 6 x,field 8 x)
noncomputable def firstNode_computes : PolyComputes firstNode := (field_computes 6).pair (field_computes 8)
noncomputable def scanInput (x : List Bool) : List Bool :=
  encode [field 0 x,field 4 x,nextQ x,crossCtx x,field 9 x,firstNode x,BinaryRegularChain.run (chainInput x)]
noncomputable def scanInput_computes : PolyComputes scanInput :=
  list_computes [field 0,field 4,nextQ,crossCtx,field 9,firstNode,BinaryRegularChain.run ∘ chainInput] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨field_computes _⟩
    · exact ⟨field_computes _⟩
    · exact ⟨nextQ_computes⟩
    · exact ⟨crossCtx_computes⟩
    · exact ⟨field_computes _⟩
    · exact ⟨firstNode_computes⟩
    · exact ⟨chainInput_computes.comp BinaryRegularChain.run_computes⟩)
noncomputable def run : List Bool → List Bool := BinaryScan.run ∘ scanInput
noncomputable def run_computes : PolyComputes run := scanInput_computes.comp BinaryScan.run_computes
def pack {m : ℕ} (base : List Bool) (key spare k n q : ℕ) (H G : List (Label (Fin m)))
    (T U : List (List (Label (Fin m)))) : List Bool :=
  encode [base,key.bits,spare.bits,k.bits,List.replicate n true,List.replicate q true,labels H,labels G,historyBits T,historyBits U]
lemma chainInput_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (key spare k n q : ℕ) (H G : List (Label (Fin m)))
    (T U : List (List (Label (Fin m)))) :
    chainInput (pack (BinaryFiniteContext.pack distance loc F Q v z lam) key spare k n q H G T U)=
      BinaryRegularChain.pack (BinaryFiniteContext.pack distance loc F Q v z lam) key spare (BinaryLabel.orderedSort F) H G := by
  simp only [chainInput,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryRegular.base_F,BinaryRegularChain.pack,setBits,BinaryLabel.orderedSort]
lemma crossCtx_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (key spare k n q : ℕ) (H G : List (Label (Fin m)))
    (T U : List (List (Label (Fin m)))) :
    crossCtx (pack (BinaryFiniteContext.pack distance loc F Q v z lam) key spare k n q H G T U)=BinaryCross.ctxBits F Q k := by
  simp only [crossCtx,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryFiniteContext.pack,BinaryCross.ctxBits]
lemma run_pack {m d : ℕ} [PseudoMetricSpace (Label (Fin m))]
    (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F B Q : Finset (Label (Fin m))) (v lam : ℚ) (eta : ℝ) (key spare k n q : ℕ)
    (hc : CorrectCompletion loc F (v:ℝ) ((1+v^2)^q:ℚ) lam
      (FiniteLabelContinuation.complete loc (rows distance) F v ((1+v^2)^q) lam))
    (hv : (0:ℝ)<v) (hvsmall : (v:ℝ)<1/6) (hlam : (0:ℝ)<lam) (heta : 0≤eta)
    (hQ : Q⊆F∪B) (hdis : Disjoint F B)
    (hrow : ∀ i∈F,bidRow loc (1-3*(v:ℝ)) ((1+(v:ℝ)^2)^q) Q i≤lam)
    (hfresh : ∀ i∈F,copy key i∉F∪B) (hco : ∀ i∈F,∀ j,dist (loc j) i=dist (loc j) (copy key i))
    (H G : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) (hHr : ∀ i∈H,i∈F) (hGr : ∀ i∈G,i∈F)
    (hH : Valid loc F B Q v ((1+(v:ℝ)^2)^q) lam eta H) (hG : Valid loc F B Q v ((1+(v:ℝ)^2)^q) lam eta G) :
    run (pack (BinaryFiniteContext.pack distance loc F Q v ((1+v^2)^q) lam) key spare k n q H G T U)=
      BinaryCross.resultBits (FiniteLabelCrossing.run loc (rows distance) F Q v lam q n k (copy key) (copy spare) H G T U) := by
  have hz : (((1+v^2)^q:ℚ):ℝ)=(1+(v:ℝ)^2)^q := by push_cast; rfl
  have hh:=BinaryRegularChain.run_pack distance loc F B Q v ((1+v^2)^q) lam eta key spare (BinaryLabel.orderedSort F) hc
    hv hvsmall (by rw [hz]; positivity) hlam heta hQ hdis (by simpa only [hz] using hrow) hfresh hco H G hHr hGr
    (by simpa only [hz] using hH) (by simpa only [hz] using hG)
  simp only [run,Function.comp_apply,scanInput,chainInput_pack,crossCtx_pack,hh]
  simp only [nextQ,firstNode,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  change BinaryScan.run (BinaryScan.pack (BinaryFiniteContext.pack distance loc F Q v ((1+v^2)^q) lam) F Q k n (q+1)
    U H T (CanonicalMergeRefinement.regularChain F (BinaryLabel.orderedSort F)
      (FiniteLabelContinuation.complete loc (rows distance) F v ((1+v^2)^q) lam) Q (copy key) (copy spare) H G))=_
  exact BinaryScan.run_pack distance loc F Q v ((1+v^2)^q) lam k n (q+1) U H T _
end MetricKMedianRecovery.BitMachine.BinaryFiniteCross

end OAI
