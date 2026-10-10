import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.WordExtras

namespace OAI

namespace MetricKMedianRecovery.BitMachine.RationalMatrix
lemma rowEncode_injective {d : ℕ} : Function.Injective (@rowEncode d) := by
  intro a b h
  simp only [rowEncode_eq] at h
  have hf := List.ofFn_injective (WordList.encode_injective h)
  funext j
  have hd := congrArg BinaryRational.decode (congrFun hf j)
  simpa only [BinaryRational.decode_encode] using hd
end MetricKMedianRecovery.BitMachine.RationalMatrix
namespace MetricKMedianRecovery.BitMachine.BinaryLength
open WordOperations WordList RationalLeaves CanonicalLengthView BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryLabelMatrix.row
def planBits {m : ℕ} : Plan (Label (Fin m)) → List Bool
  | .free i f=>encode [(0:ℕ).bits,BinaryLabel.encode i,BinaryLabel.encode f,[],[]]
  | .paid C T i=>encode [(1:ℕ).bits,BinaryLabel.encode i,[],labels C,labels T]
def ctxBits {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Label (Fin m)))
    (R H G : List (Label (Fin m))) : List Bool :=
  encode [setBits F,labels R,labels H,labels G,pairBits (Rectangular.encode distance,List.replicate d true)]
def cf (n : ℕ) : List Bool → List Bool := field n ∘ extractPrefix
def pf (n : ℕ) : List Bool → List Bool := field n ∘ discardPrefix
noncomputable def cf_computes (n : ℕ) : PolyComputes (cf n) := extractPrefix_computes.comp (field_computes n)
noncomputable def pf_computes (n : ℕ) : PolyComputes (pf n) := discardPrefix_computes.comp (field_computes n)
noncomputable def isFree (x : List Bool) : Bool := decide (value (pf 0 x)=0)
noncomputable def isFree_computes : PolyComputes (fun x=>[isFree x]) := by
  simpa only [isFree,value_bits] using NatOps.eq (pf_computes 0) (const_computes (0:ℕ).bits)
noncomputable def source (x : List Bool) : List Bool :=
  if isFree x then cf 2 x else pf 3 x++cons (pf 1 x) (pf 4 x)
noncomputable def source_computes : PolyComputes source := isFree_computes.cond (cf_computes 2)
  ((pf_computes 3).append (cons_computes (pf_computes 1) (pf_computes 4)))
noncomputable def target (x : List Bool) : List Bool :=
  if isFree x then cf 2 x++cons (pf 2 x) [] else pf 3 x++pf 4 x
noncomputable def target_computes : PolyComputes target := isFree_computes.cond
  ((cf_computes 2).append (cons_computes (pf_computes 2) (const_computes [])))
  ((pf_computes 3).append (pf_computes 4))
noncomputable def rootIn (x : List Bool) : Bool := BinaryLabel.contains (pairBits (pf 1 x,cf 0 x))
noncomputable def rootIn_computes : PolyComputes (fun x=>[rootIn x]) :=
  ((pf_computes 1).pair (cf_computes 0)).comp BinaryLabel.contains_computes
noncomputable def freeOut (x : List Bool) : Bool := !BinaryLabel.contains (pairBits (pf 2 x,cf 0 x))
noncomputable def freeOut_computes : PolyComputes (fun x=>[freeOut x]) :=
  (((pf_computes 2).pair (cf_computes 0)).comp BinaryLabel.contains_computes).not
noncomputable def row (n : ℕ) (x : List Bool) : List Bool := BinaryLabelMatrix.row (pairBits (cf 4 x,pf n x))
noncomputable def row_computes (n : ℕ) : PolyComputes (row n) :=
  ((cf_computes 4).pair (pf_computes n)).comp BinaryLabelMatrix.row_computes
noncomputable def sameRow (x : List Bool) : Bool := WordEq.eq (pairBits (row 1 x,row 2 x))
noncomputable def sameRow_computes : PolyComputes (fun x=>[sameRow x]) :=
  ((row_computes 1).pair (row_computes 2)).comp WordEq.eq_computes
noncomputable def extra (x : List Bool) : Bool := if isFree x then freeOut x && sameRow x else true
noncomputable def extra_computes : PolyComputes (fun x=>[extra x]) := by
  have h:=isFree_computes.cond (freeOut_computes.and sameRow_computes) (const_computes [true])
  convert h using 1
  funext x
  unfold extra
  split_ifs <;> rfl
noncomputable def accepts (x : List Bool) : Bool := rootIn x &&
  (WordEq.eq (pairBits (cf 2 x,source x)) && (WordEq.eq (pairBits (cf 3 x,target x)) && extra x))
noncomputable def accepts_computes : PolyComputes (fun x=>[accepts x]) := rootIn_computes.and
  (((cf_computes 2).pair source_computes |>.comp WordEq.eq_computes).and
    (((cf_computes 3).pair target_computes |>.comp WordEq.eq_computes).and extra_computes))
lemma accepts_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Label (Fin m)))
    (R H G : List (Label (Fin m))) (J : Plan (Label (Fin m))) :
    accepts (pairBits (ctxBits distance F R H G,planBits J))=
      decide (CanonicalLengthView.accepts (rows distance) F H G J) := by
  apply Bool.eq_iff_iff.mpr
  cases J <;> simp only [accepts,rootIn,source,target,extra,isFree,freeOut,sameRow,row,cf,pf,
    Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,ctxBits,planBits,
    field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,value_bits,
    BinaryLabel.contains_setBits,BinaryLabelMatrix.row_pack,WordEq.eq_pair]
  · rename_i i f
    simp only [decide_true,ite_true,decide_eq_true_eq,eq_self,Bool.and_eq_true,true_and,
      Bool.not_eq_true',decide_eq_false_iff_not]
    rw [show cons (BinaryLabel.encode f) []=labels [f] from rfl, ←BinaryFiniteContext.labels_append]
    simp only [BinaryFiniteContext.labels_injective.eq_iff,RationalMatrix.rowEncode_injective.eq_iff,
      CanonicalLengthView.accepts]
    rw [funext_iff]
    tauto
  · rename_i C T i
    simp only [Nat.one_ne_zero,decide_false,Bool.false_eq_true,ite_false,decide_eq_true_eq,
      Bool.and_eq_true,and_true]
    rw [←BinaryFiniteContext.labels_cons,←BinaryFiniteContext.labels_append,←BinaryFiniteContext.labels_append]
    simp only [BinaryFiniteContext.labels_injective.eq_iff,CanonicalLengthView.accepts]
end MetricKMedianRecovery.BitMachine.BinaryLength

end OAI
