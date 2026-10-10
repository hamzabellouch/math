import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.CrossCount

namespace OAI

namespace MetricKMedianRecovery.BitMachine
noncomputable def PolyComputes.boolCond {p f g : List Bool → Bool}
    (hp : PolyComputes (fun x=>[p x])) (hf : PolyComputes (fun x=>[f x]))
    (hg : PolyComputes (fun x=>[g x])) : PolyComputes (fun x=>[if p x then f x else g x]) := by
  convert hp.cond hf hg using 1
  funext x
  split_ifs <;> rfl
end MetricKMedianRecovery.BitMachine
namespace MetricKMedianRecovery.BitMachine.BinaryCross
open WordOperations WordList RationalLeaves BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] paid finalCount

def resultBits {m : ℕ} : CanonicalMergeCrossing.Result (Label (Fin m)) → List Bool
  | .success H T=>encode [(0:ℕ).bits,nodeBits (H,T),[]]
  | .common H T U=>encode [(1:ℕ).bits,nodeBits (H,T),historyBits U]
  | .sensitive H G T U=>encode [(2:ℕ).bits,nodeBits (H,T),nodeBits (G,U)]
def pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
    (P R : List (Label (Fin m)) × List (List (Label (Fin m)))) : List Bool :=
  pairBits (ctxBits F Q k,pairBits (nodeBits P,nodeBits R))
noncomputable def leftNode : List Bool → List Bool := extractPrefix ∘ discardPrefix
noncomputable def rightNode : List Bool → List Bool := discardPrefix ∘ discardPrefix
noncomputable def leftNode_computes : PolyComputes leftNode := discardPrefix_computes.comp extractPrefix_computes
noncomputable def rightNode_computes : PolyComputes rightNode := discardPrefix_computes.comp discardPrefix_computes
noncomputable def leftData (x : List Bool) : List Bool := pairBits (extractPrefix x,leftNode x)
noncomputable def rightData (x : List Bool) : List Bool := pairBits (extractPrefix x,rightNode x)
noncomputable def leftData_computes : PolyComputes leftData := extractPrefix_computes.pair leftNode_computes
noncomputable def rightData_computes : PolyComputes rightData := extractPrefix_computes.pair rightNode_computes
noncomputable def leftPaid : List Bool → List Bool := paid ∘ leftData
noncomputable def rightPaid : List Bool → List Bool := paid ∘ rightData
noncomputable def leftPaid_computes : PolyComputes leftPaid := leftData_computes.comp paid_computes
noncomputable def rightPaid_computes : PolyComputes rightPaid := rightData_computes.comp paid_computes
noncomputable def leftLength : List Bool → List Bool := lengthBits ∘ extractPrefix ∘ leftNode
noncomputable def rightLength : List Bool → List Bool := lengthBits ∘ extractPrefix ∘ rightNode
noncomputable def leftLength_computes : PolyComputes leftLength := (leftNode_computes.comp extractPrefix_computes).comp lengthBits_computes
noncomputable def rightLength_computes : PolyComputes rightLength := (rightNode_computes.comp extractPrefix_computes).comp lengthBits_computes
noncomputable def forward (x : List Bool) : Bool :=
  if decide (value (leftPaid x)=value (rightPaid x)) then decide (value (leftLength x)<value (rightLength x))
  else decide (value (rightPaid x)<value (leftPaid x))
noncomputable def forward_computes : PolyComputes (fun x=>[forward x]) :=
  (NatOps.eq leftPaid_computes rightPaid_computes).boolCond
    (NatOps.lt leftLength_computes rightLength_computes) (NatOps.lt rightPaid_computes leftPaid_computes)
lemma forward_pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
    (H G : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) :
    forward (pack F Q k (H,T) (G,U))=CanonicalMergeCrossing.forward F Q H G := by
  simp only [forward,leftPaid,rightPaid,leftData,rightData,leftNode,rightNode,leftLength,rightLength,pack,
    Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits]
  rw [paid_pack,paid_pack]
  simp only [nodeBits,extractPrefix_pairBits,labels,lengthBits_encode,List.length_map,value_bits,
    decide_eq_true_eq,CanonicalMergeCrossing.forward]

noncomputable def mixed (x : List Bool) : List Bool := pairBits (extractPrefix (rightNode x),discardPrefix (leftNode x))
noncomputable def mixed_computes : PolyComputes mixed :=
  (rightNode_computes.comp extractPrefix_computes).pair (leftNode_computes.comp discardPrefix_computes)
noncomputable def mixedCount (x : List Bool) : List Bool := finalCount (pairBits (extractPrefix x,mixed x))
noncomputable def mixedCount_computes : PolyComputes mixedCount :=
  (extractPrefix_computes.pair mixed_computes).comp finalCount_computes
noncomputable def successNode (x : List Bool) : List Bool := encode [(0:ℕ).bits,x,[]]
noncomputable def successNode_computes : PolyComputes successNode :=
  list_computes [fun _=>(0:ℕ).bits,id,fun _=>[]] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl
    · exact ⟨const_computes _⟩
    · exact ⟨id_computes⟩
    · exact ⟨const_computes _⟩)
noncomputable def taggedPair (tag : ℕ) (x : List Bool) : List Bool := encode [tag.bits,extractPrefix x,discardPrefix x]
noncomputable def taggedPair_computes (tag : ℕ) : PolyComputes (taggedPair tag) :=
  list_computes [fun _=>tag.bits,extractPrefix,discardPrefix] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl
    · exact ⟨const_computes _⟩
    · exact ⟨extractPrefix_computes⟩
    · exact ⟨discardPrefix_computes⟩)
noncomputable def mixedCommon (x : List Bool) : List Bool := taggedPair 1 (pairBits (mixed x,discardPrefix (rightNode x)))
noncomputable def mixedCommon_computes : PolyComputes mixedCommon :=
  (mixed_computes.pair (rightNode_computes.comp discardPrefix_computes)).comp (taggedPair_computes 1)
noncomputable def directed (x : List Bool) : List Bool :=
  if decide (value (leftLength x)=value (rightLength x)) then
    if decide (value (mixedCount x)=value (cf 2 x)) then successNode (mixed x) else mixedCommon x
  else taggedPair 2 (discardPrefix x)
noncomputable def directed_computes : PolyComputes directed :=
  (NatOps.eq leftLength_computes rightLength_computes).cond
    ((NatOps.eq mixedCount_computes (cf_computes 2)).cond (mixed_computes.comp successNode_computes) mixedCommon_computes)
    (discardPrefix_computes.comp (taggedPair_computes 2))
lemma mixed_pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
    (H G : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) :
    mixed (pack F Q k (H,T) (G,U))=nodeBits (G,T) := by
  simp only [mixed,pack,leftNode,rightNode,Function.comp_apply,nodeBits,extractPrefix_pairBits,discardPrefix_pairBits]
lemma directed_pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
    (H G : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) :
    directed (pack F Q k (H,T) (G,U))=resultBits (CanonicalMergeCrossing.directed F Q k H G T U) := by
  simp only [directed,mixedCommon,mixedCount,mixed_pack]
  simp only [leftLength,rightLength,leftNode,rightNode,pack,Function.comp_apply,extractPrefix_pairBits,
    discardPrefix_pairBits]
  rw [finalCount_pack]
  simp only [cf,Function.comp_apply,extractPrefix_pairBits,ctxBits,nodeBits,labels,lengthBits_encode,
    List.length_map,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    value_bits,decide_eq_true_eq]
  unfold CanonicalMergeCrossing.directed
  split_ifs <;> simp only [successNode,taggedPair,resultBits,nodeBits,labels,extractPrefix_pairBits,discardPrefix_pairBits]

noncomputable def flipped (x : List Bool) : List Bool := pairBits (extractPrefix x,pairBits (rightNode x,leftNode x))
noncomputable def flipped_computes : PolyComputes flipped := extractPrefix_computes.pair (rightNode_computes.pair leftNode_computes)
noncomputable def edge (x : List Bool) : List Bool := if forward x then directed x else directed (flipped x)
noncomputable def edge_computes : PolyComputes edge := forward_computes.cond directed_computes (flipped_computes.comp directed_computes)
lemma edge_pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
    (H G : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) :
    edge (pack F Q k (H,T) (G,U))=resultBits (CanonicalMergeCrossing.edge F Q k H G T U) := by
  have hf : flipped (pack F Q k (H,T) (G,U))=pack F Q k (G,U) (H,T) := by
    simp only [flipped,pack,leftNode,rightNode,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits]
  rw [edge,forward_pack,hf]
  unfold CanonicalMergeCrossing.edge
  split_ifs <;> rw [directed_pack]
end MetricKMedianRecovery.BitMachine.BinaryCross

end OAI
