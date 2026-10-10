import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalDataLog
import OAI.Computability.QuantumFactoring.VerifiedTreeBounds

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic

/-- Fixed-capacity, first-match read-only lookup. Every iteration is an explicit
Boolean network; malformed/missing labels use the zero word. -/
def lookupWordNet {k q w : ℕ} (query : BooleanNetwork k q) :
    List (BooleanNetwork k q × BooleanNetwork k w)→BooleanNetwork k w
  | []=>wordConstant 0
  | a::as=>wordMux (equalOn query a.1) a.2 (lookupWordNet query as)

def lookupWord {q w : ℕ} (query : Basis q) : List (Basis q × Basis w)→Basis w
  | []=>fun _=>false
  | a::as=>if query=a.1 then a.2 else lookupWord query as

lemma lookupWordNet_value {k q w : ℕ} (query : BooleanNetwork k q)
    (rows : List (BooleanNetwork k q × BooleanNetwork k w)) (x : Basis k) :
    (lookupWordNet query rows).eval x=lookupWord (query.eval x)
      (rows.map (fun a=>(a.1.eval x,a.2.eval x))) := by
  induction rows with
  | nil=>
    funext i
    simp [lookupWordNet,lookupWord,wordConstant]
  | cons a as ih=>
    have he : (bitsValue (query.eval x)).toNat=(bitsValue (a.1.eval x)).toNat ↔
        query.eval x=a.1.eval x := by
      exact ⟨fun h=>(bitsEquiv q).injective (BitVec.eq_of_toNat_eq h),fun h=>by rw [h]⟩
    rw [lookupWordNet,wordMux_eval,ih]
    simp only [List.map_cons,lookupWord,equalOn_value,he]

lemma lookupWordNet_count {k q w a b : ℕ} (query : BooleanNetwork k q)
    (rows : List (BooleanNetwork k q × BooleanNetwork k w))
    (hr : ∀ r∈rows,r.1.net.count≤a ∧ r.2.net.count≤b) :
    (lookupWordNet query rows).net.count≤
      w+rows.length*(query.net.count+a+b+96*q+21+7*w) := by
  induction rows with
  | nil=>simp only [lookupWordNet,wordConstant_count,List.length_nil,Nat.zero_mul,Nat.add_zero,le_refl]
  | cons r rs ih=>
    have h:=hr r (by simp)
    have ht:=ih (fun r hh=>hr r (List.mem_cons_of_mem _ hh))
    have he:=equalOn_count query r.1
    have hc:=wordMux_count (equalOn query r.1) r.2 (lookupWordNet query rs)
    simp only [lookupWordNet,List.length_cons]
    nlinarith

namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

/-- The rows are at their true retained locations. This construction has no
quantum conditioning and does not evaluate a factorization operation. -/
def logNets : (t : ℕ)→List (BooleanNetwork (M.width t) n ×
    BooleanNetwork (M.width t) (tensorWidth n n))
  | 0=>[]
  | t+1=>(M.rowQuery t,(M.lastNodeNet t).comp (PhysicalTree.nodeResult n))::
      ((logNets t).map (fun r=>((M.previousNet t).comp r.1,(M.previousNet t).comp r.2)))

lemma logNets_length (t : ℕ) : (M.logNets t).length=t := by
  induction t with
  | zero=>rfl
  | succ t ih=>simp only [logNets,List.length_cons,List.length_map,ih]

lemma logNets_counts (t : ℕ) : ∀ r∈M.logNets t,
    r.1.net.count≤M.query.net.count ∧ r.2.net.count≤PhysicalNode.resultBound n := by
  induction t with
  | zero=>simp only [logNets,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | succ t ih=>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · refine ⟨(M.rowQuery_count t).le,?_⟩
      simpa only [count_comp,M.lastNodeNet_count,Nat.zero_add] using PhysicalTree.nodeResult_count n
    · change r ∈ (M.logNets t).map (fun a=>((M.previousNet t).comp a.1,
        (M.previousNet t).comp a.2)) at hr
      obtain ⟨a,ha,he⟩:=List.mem_map.mp hr
      subst r
      simpa only [count_comp,M.previousNet_count,Nat.zero_add] using ih a ha

lemma logNets_values (x : Basis c) (t : ℕ) (h : Trace n t) :
    (M.logNets t).map (fun r=>((bitsValue (r.1.eval (M.encoded x t h))).toNat,
      SortedWords.numbers (List.ofFn (fun i=>(tensorLayout n n).symm
        (r.2.eval (M.encoded x t h)) i))))=M.dataLog x t h := by
  induction t with
  | zero=>rfl
  | succ t ih=>
    change (_::List.map _ (List.map _ (M.logNets t)))=_
    simp only [List.map_map,Function.comp_def,eval_comp,M.previousNet_encoded,
      M.lastNodeNet_encoded,M.rowQuery_encoded]
    rw [ih]
    simp only [dataLog,PhysicalTree.nodeWords,PhysicalTree.resultFields,eval_comp,
      tensorSelect_inverse]
end NodeMachine
end ExactQuantumFactoring


end

end OAI
