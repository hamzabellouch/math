import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.RawSlices
import OAI.Combinatorics.KMedianRecovery.Encoding.MatrixRows
import OAI.Combinatorics.KMedianRecovery.Encoding.UniformWord

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySeed
open WordOperations WordList BinaryArithmetic
noncomputable def product : ℕ→List Bool→List Bool
  | 0,_ => (1:ℕ).bits
  | d+1,x => (value (UnaryResources.lengthBits (head x))*value (product d (tail x))).bits
noncomputable def product_computes (d : ℕ) : PolyComputes (product d) := by
  induction d with
  | zero=>exact const_computes _
  | succ d ih=>exact NatOps.mul (WordList.head_computes.comp UnaryResources.lengthBits_computes) (WordList.tail_computes.comp ih)
def shape (ds : List ℕ) : List Bool := encode (ds.map (fun n=>List.replicate n true))
lemma shape_tail (n : ℕ) (ns : List ℕ) : WordList.tail (shape (n::ns))=shape ns := by
  simp only [shape,List.map_cons,encode,tail_cons]
lemma product_shape (ds : List ℕ) : product ds.length (shape ds)=ds.prod.bits := by
  induction ds with
  | nil=>rfl
  | cons d ds ih=>simp only [List.length_cons,product,shape,List.map_cons,encode,head_cons,tail_cons,
      UnaryResources.lengthBits_eq,List.length_replicate,value_bits,List.prod_cons] at ih ⊢; rw [ih,value_bits]
noncomputable def width (d : ℕ) (x : List Bool) : List Bool := product (d+1) (tail (extractPrefix (extractPrefix x)))
noncomputable def width_computes (d : ℕ) : PolyComputes (width d) :=
  ((extractPrefix_computes.comp extractPrefix_computes).comp WordList.tail_computes).comp (product_computes _)
noncomputable def chunk (d : ℕ) (x : List Bool) : List Bool := RawTake.run (pairBits (width d x,
  RawDrop.run (pairBits ((value (width d x)*value (discardPrefix x)).bits,discardPrefix (extractPrefix x)))))
attribute [local irreducible] width RawTake.run RawDrop.run
noncomputable def chunk_computes (d : ℕ) : PolyComputes (chunk d) :=
  ((width_computes d).pair (((NatOps.mul (width_computes d) discardPrefix_computes).pair
    (extractPrefix_computes.comp discardPrefix_computes)).comp RawDrop.run_computes)).comp RawTake.run_computes
noncomputable def child (d : ℕ) (x : List Bool) : List Bool :=
  pairBits (tail (extractPrefix (extractPrefix x)),chunk d x)
noncomputable def child_computes (d : ℕ) : PolyComputes (child d) :=
  ((extractPrefix_computes.comp extractPrefix_computes).comp WordList.tail_computes).pair (chunk_computes d)
noncomputable def indices (x : List Bool) : List Bool := BinaryEllipsoidInitial.indices (head (extractPrefix x))
noncomputable def indices_computes : PolyComputes indices :=
  (extractPrefix_computes.comp WordList.head_computes).comp BinaryEllipsoidInitial.indices_computes
noncomputable def nest : ℕ→List Bool→List Bool
  | 0,x =>normalizeBig (discardPrefix x)
  | d+1,x =>mapWith (fun y=>nest d (child d y)) (pairBits (x,indices x))
noncomputable def nest_computes (d : ℕ) : PolyComputes (nest d) := by
  induction d with
  | zero=>exact discardPrefix_computes.comp normalizeBig_computes
  | succ dimension inductionHypothesis=>
    change PolyComputes (fun input=>mapWith (fun word=>nest dimension (child dimension word))
      (pairBits (input,indices input)))
    simpa only [Function.comp_def,id_eq] using
      (id_computes.pair indices_computes).comp
        (mapWith_computes ((child_computes dimension).comp inductionHypothesis))
def Tensor : List ℕ→ℕ→Type
  | [],b =>Fin b→Bool
  | n::ns,b =>Fin n→Tensor ns b
def raw : {ds : List ℕ}→{b : ℕ}→Tensor ds b→List Bool
  | [],_,s=>List.ofFn s
  | _::_,_,s=>(List.ofFn (fun i=>raw (s i))).flatten
noncomputable def parsed : {ds : List ℕ}→{b : ℕ}→Tensor ds b→List Bool
  | [],b,s=>(Categorical.uniformBits b s).val.bits
  | _::_,_,s=>encode (List.ofFn (fun i=>parsed (s i)))
lemma raw_length {ds : List ℕ} {b : ℕ} (s : Tensor ds b) : (raw s).length=(ds++[b]).prod := by
  induction ds with
  | nil=>change (List.ofFn (s:Fin b→Bool)).length = b*1
         rw [Nat.mul_one]
         exact List.length_ofFn
  | cons n ns ih=>
    change (List.ofFn (fun i:Fin n=>raw (s i))).flatten.length = ((n::ns)++[b]).prod
    simp only [List.length_flatten,List.map_ofFn,Function.comp_def,ih,List.cons_append,List.prod_cons]
    rw [List.sum_ofFn]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
lemma chunk_tensor (n : ℕ) (ns : List ℕ) (b : ℕ) (s : Tensor (n::ns) b) (i : Fin n) :
    chunk ns.length (pairBits (pairBits (shape (n::ns++[b]),raw s),i.val.bits))=raw (s i) := by
  have hw : width ns.length (pairBits (pairBits (shape (n::ns++[b]),raw s),i.val.bits))=(ns++[b]).prod.bits := by
    rw [width,extractPrefix_pairBits,extractPrefix_pairBits,List.cons_append,shape_tail]
    rw [show ns.length+1=(ns++[b]).length by simp,product_shape]
  rw [chunk,hw,discardPrefix_pairBits,value_bits,extractPrefix_pairBits,discardPrefix_pairBits,
    RawDrop.run_encode,RawTake.run_pack]
  rw [value_bits]
  change ((List.ofFn (fun j=>raw (s j))).flatten.drop ((ns++[b]).prod*i.val)).take (ns++[b]).prod=raw (s i)
  rw [BinaryInputParser.Rows.slice_flatten _ _ (by
    intro x hx; obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hx; exact raw_length (s j)),List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some]
lemma nest_tensor {ds : List ℕ} {b : ℕ} (s : Tensor ds b) :
    nest ds.length (pairBits (shape (ds++[b]),raw s))=parsed s := by
  induction ds with
  | nil=>simpa only [List.length_nil,nest,discardPrefix_pairBits,raw,parsed] using normalizeBig_ofFn b s
  | cons n ns ih=>
    simp only [List.length_cons,nest,indices,extractPrefix_pairBits,shape,List.cons_append,List.map_cons,
      encode,head_cons,BinaryEllipsoidInitial.indices_replicate,mapWith_ofFn]
    change encode (List.ofFn (fun i:Fin n=>nest ns.length (child ns.length
      (pairBits (pairBits (shape (n::ns++[b]),raw s),i.val.bits)))))=encode (List.ofFn (fun i=>parsed (s i)))
    congr 1
    apply congrArg List.ofFn
    funext i
    rw [child,chunk_tensor]
    rw [extractPrefix_pairBits,extractPrefix_pairBits,List.cons_append,shape_tail]
    exact ih (s i)
end MetricKMedianRecovery.BitMachine.BinarySeed

end OAI
