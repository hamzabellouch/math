import Mathlib
import OAI.Computability.QuantumFactoring.TableOrderCircuit
import OAI.Computability.QuantumFactoring.VerifiedTreeBounds
import OAI.Computability.QuantumFactoring.CanonicalResidueCircuit
import OAI.Computability.QuantumFactoring.RetrospectiveLists
import OAI.Computability.QuantumFactoring.RetainedTable

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

def retainedCanonical (t : ℕ) (a m : BooleanNetwork (M.width t) n) : BooleanNetwork (M.width t) 1 :=
  tableCanonicalNet (tableNets (M.fieldRows t)) a m

lemma retainedCanonical_exact {N P d : ℕ} (hn : 2≤n) (t : ℕ)
    (a m : BooleanNetwork (M.width t) n) (x : Basis c) (r : Trace n t)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hd : 2≤d) (hdiv : d∣P) (hm : (bitsValue (m.eval (M.encoded x t r))).toNat=d) :
    (M.retainedCanonical t a m).eval (M.encoded x t r) 0=true ↔
      dataCanonicalResidue (trueData P)
        (bitsValue (a.eval (M.encoded x t r))).toNat d := by
  have he:=tableNets_values hn (M.fieldRows t) (M.encoded x t r)
  rw [M.fieldRows_values] at he
  have hp : ∀ p∈tableNets (M.fieldRows t),
      ((bitsValue (p.eval (M.encoded x t r))).toNat).Prime := by
    intro p hp
    apply PhysicalTree.tableFactors_prime hc
    rw [←he]
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  rw [retainedCanonical,tableCanonicalNet_value _ a m _ (by omega) hp,he,hm]
  exact tableCanonical_correct (by omega) hd (hm ▸ (bitsValue (m.eval (M.encoded x t r))).isLt.le)
    hdiv (PhysicalTree.tableFactors_prime hc)
    (PhysicalTree.tableFactors_cover hc hP hP0 (by omega) hdiv) _

lemma retainedCanonical_count {b : ℕ} (t : ℕ) (a m : BooleanNetwork (M.width t) n)
    (ha : a.net.count≤b) (hm : m.net.count≤b)
    (hq : M.query.net.count≤b) (hr : PhysicalNode.resultBound n≤b) :
    (M.retainedCanonical t a m).net.count≤tableCanonicalBound n (t*n) (3*b+220*n+50) := by
  have hf:=tableNets_counts (M.fieldRows t) (c:=b) (by
    intro r hh
    have H:=M.fieldRows_counts t r hh
    exact ⟨H.1.trans hq,fun p hp=>(H.2 p hp).trans hr⟩)
  have h:=tableCanonicalNet_count (tableNets (M.fieldRows t)) a m hf
    (ha.trans (by omega)) (hm.trans (by omega))
  rwa [M.fieldRows_table_length] at h
end NodeMachine

namespace TransitionWords

def readNet {k n K : ℕ} (y : BooleanNetwork k (n*(K+1))) (i : Fin K) : BooleanNetwork k n :=
  y.rewire (fun j=>Fin.cast (Nat.mul_comm _ _) (finProdFinEquiv (i.castSucc,j)))
lemma readNet_eval {k n K : ℕ} (y : BooleanNetwork k (n*(K+1))) (i : Fin K) (x : Basis k) :
    (readNet y i).eval x=read (y.eval x) i := rfl

/-- A polynomial-size literal shape check, including the otherwise-unused last
word. It does not construct the unknown canonical CRT residue. -/
def firstOnly {k n K : ℕ} (a : BooleanNetwork k n) : BooleanNetwork k (n*(K+1)) :=
  encodeNet (fun i : Fin K=>if i.val=0 then a else wordConstant (BitVec.ofNat n 0))
lemma firstOnly_eval {k n K : ℕ} (a : BooleanNetwork k n) (x : Basis k) :
    (firstOnly (K:=K) a).eval x=encode (fun i : Fin K=>if i.val=0 then a.eval x else OrderTrial.natBasis n 0) := by
  rw [firstOnly,encodeNet_eval]
  congr 1
  funext i
  split_ifs
  · rfl
  · funext j
    simp only [wordConstant,eval_vector,eval_constant,OrderTrial.natBasis]
end TransitionWords

namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

def retainedCanonicalList (hn : 0<n) (t : ℕ) (m : BooleanNetwork (M.width t) n)
    (y : BooleanNetwork (M.width t) (n*(n^5+1))) : BooleanNetwork (M.width t) 1 :=
  let a:=TransitionWords.readNet y ⟨0,pow_pos hn 5⟩
  (M.retainedCanonical t a m).band (equalOn y (TransitionWords.firstOnly a))

lemma retainedCanonicalList_exact {N P d : ℕ} (hn : 2≤n) (t : ℕ)
    (m : BooleanNetwork (M.width t) n) (y : BooleanNetwork (M.width t) (n*(n^5+1)))
    (x : Basis c) (r : Trace n t) (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hd : 2≤d) (hdiv : d∣P) (hm : (bitsValue (m.eval (M.encoded x t r))).toNat=d) :
    (M.retainedCanonicalList (by omega) t m y).eval (M.encoded x t r) 0=true ↔
      dataCanonicalList (trueData P) d n (by omega) (y.eval (M.encoded x t r)) := by
  change (M.retainedCanonicalList _ t m y).eval (M.encoded x t r) 0=true ↔
    dataCanonicalResidue (trueData P) (bitsValue (TransitionWords.read (y.eval (M.encoded x t r))
      ⟨0,pow_pos (by omega : 0<n) 5⟩)).toNat d ∧
    y.eval (M.encoded x t r)=TransitionWords.encode (fun i : Fin (n^5)=>if i.val=0 then
      TransitionWords.read (y.eval (M.encoded x t r)) ⟨0,pow_pos (by omega : 0<n) 5⟩ else OrderTrial.natBasis n 0)
  let aa : BooleanNetwork (M.width t) n := TransitionWords.readNet y ⟨0,pow_pos (by omega : 0<n) 5⟩
  have hcan := M.retainedCanonical_exact hn t aa m x r hc hP hP0 hd hdiv hm
  have hshape : (equalOn y (TransitionWords.firstOnly (K:=n^5) aa)).eval (M.encoded x t r) 0=true ↔
      y.eval (M.encoded x t r)=TransitionWords.encode (fun i : Fin (n^5)=>
        if i.val=0 then aa.eval (M.encoded x t r) else OrderTrial.natBasis n 0) := by
    rw [equalOn_value y (TransitionWords.firstOnly (K:=n^5) aa),TransitionWords.firstOnly_eval]
    exact ⟨fun h=>(bitsEquiv _).injective (BitVec.eq_of_toNat_eq h),congrArg (fun z=>(bitsValue z).toNat)⟩
  simpa only [retainedCanonicalList,eval_band,Bool.and_eq_true,aa,
    TransitionWords.readNet_eval] using and_congr hcan hshape
end NodeMachine
end ExactQuantumFactoring


end

end OAI
