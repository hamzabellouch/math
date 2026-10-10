import Mathlib
import OAI.Computability.QuantumFactoring.VerifiedTreeBounds
import OAI.Computability.QuantumFactoring.TableTotientCircuit
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

/-- The totient network reads only the actual retained rectangular table. -/
def retainedTotient (t : ℕ) (v : BooleanNetwork (M.width t) n) :
    BooleanNetwork (M.width t) n := tableTotient v (M.fieldRows t)

lemma retainedTotient_exact {N P m d : ℕ} (hn : 2 ≤ n) (t : ℕ)
    (v : BooleanNetwork (M.width t) n) (x : Basis c) (r : Trace n t)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hm : 2 ≤ m) (hb : m < 2^n) (hdiv : m∣P) (hd0 : 0 < d) (hdt : d∣m.totient)
    (hv : (bitsValue (v.eval (M.encoded x t r))).toNat=d) :
    (bitsValue ((M.retainedTotient t v).eval (M.encoded x t r))).toNat=d.totient := by
  apply tableTotient_exact hn v (M.fieldRows t) (M.encoded x t r)
  · rwa [M.fieldRows_values]
  · rwa [M.fieldRows_values]
  · exact hP0
  · exact hm
  · exact hb
  · exact hdiv
  · exact hd0
  · exact hdt
  · exact hv

lemma retainedTotient_count {b : ℕ} (t : ℕ) (v : BooleanNetwork (M.width t) n)
    (hv : v.net.count ≤ b) (hq : M.query.net.count ≤ b) (hr : PhysicalNode.resultBound n ≤ b) :
    (M.retainedTotient t v).net.count ≤ tableTotientBound n (t*n) b := by
  have hh:=tableTotient_count v (M.fieldRows t) hv (by
    intro r hh
    have H:=M.fieldRows_counts t r hh
    exact ⟨H.1.trans hq,fun p hp=>(H.2 p hp).trans hr⟩)
  rwa [M.fieldRows_table_length] at hh

/-- The numerator of the exact order-trial success probability, with no
recovery of an exponent record and no factorization call at runtime. -/
def retainedOrderPhi (t : ℕ) (a m : BooleanNetwork (M.width t) n) :
    BooleanNetwork (M.width t) n := M.retainedTotient t (M.retainedOrder t a m)

lemma retainedOrderPhi_exact {N P d : ℕ} (hn : 2 ≤ n) (t : ℕ)
    (a m : BooleanNetwork (M.width t) n) (x : Basis c) (r : Trace n t)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hd : 2 ≤ d) (hdiv : d∣P) (u : (ZMod d)ˣ)
    (ha : ((bitsValue (a.eval (M.encoded x t r))).toNat : ZMod d)=(u : ZMod d))
    (hm : (bitsValue (m.eval (M.encoded x t r))).toNat=d) :
    (bitsValue ((M.retainedOrderPhi t a m).eval (M.encoded x t r))).toNat=(orderOf u).totient := by
  let : NeZero d := ⟨by omega⟩
  apply M.retainedTotient_exact hn t (M.retainedOrder t a m) x r hc hP hP0 hd
  · rw [←hm]; exact (bitsValue (m.eval (M.encoded x t r))).isLt
  · exact hdiv
  · exact orderOf_pos u
  · simpa only [ZMod.card_units_eq_totient] using (orderOf_dvd_card (x:=u))
  · exact M.retainedOrder_exact hn t a m x r hc hP hP0 hd hdiv u ha hm
end NodeMachine
end ExactQuantumFactoring


end

end OAI
