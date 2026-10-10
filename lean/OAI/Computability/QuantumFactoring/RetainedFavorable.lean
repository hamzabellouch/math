import Mathlib
import OAI.Computability.QuantumFactoring.TwoAdicCircuit
import OAI.Computability.QuantumFactoring.RetainedCanonical
import OAI.Computability.QuantumFactoring.RetainedComponentOrder
import OAI.Computability.QuantumFactoring.TableFavorable

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

/-- All component computations read the same retained, verified occurrence log.
Only primes dividing the requested cofactor contribute to the comparison. -/
def retainedFavorable (t : ℕ) (a m : BooleanNetwork (M.width t) n) : BooleanNetwork (M.width t) 1 :=
  let ps:=tableNets (M.fieldRows t)
  (OrderSlots.usableOn a m).band ((all (ps.map (fun p=>all (ps.map (fun q=>
    (dividesOn p m).bnot.bor ((dividesOn q m).bnot.bor
      (sameTwoVal (M.retainedComponentOrder t a m p) (M.retainedComponentOrder t a m q)))))))).bnot)

lemma retainedFavorable_table {N P d : ℕ} (hn : 2 ≤ n) (t : ℕ)
    (a m : BooleanNetwork (M.width t) n) (x : Basis c) (r : Trace n t)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hd : 2 ≤ d) (hdiv : d∣P) (hm : (bitsValue (m.eval (M.encoded x t r))).toNat=d) :
    (M.retainedFavorable t a m).eval (M.encoded x t r) 0=true ↔
      tableFavorable (PhysicalTree.tableFactors (M.dataLog x t r)) (trueData P)
        (bitsValue (a.eval (M.encoded x t r))).toNat d n := by
  have hval:=tableNets_values hn (M.fieldRows t) (M.encoded x t r)
  rw [M.fieldRows_values] at hval
  have hp : ∀ p∈tableNets (M.fieldRows t),
      ((bitsValue (p.eval (M.encoded x t r))).toNat).Prime := by
    intro p hp
    apply PhysicalTree.tableFactors_prime hc
    rw [←hval]
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  rw [retainedFavorable,eval_band,Bool.and_eq_true,OrderSlots.usableOn_value a m _ (by omega),
    OrderSlots.Usable,ZMod.isUnit_iff_coprime,hm,tableFavorable,←hval,and_assoc]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro ha
  rw [bnot_value]
  apply not_congr
  simp only [all_eval,List.forall_mem_map,eval_bor,Bool.or_eq_true,bnot_value,
    dividesOn_value,hm,or_iff_not_imp_left,not_not]
  have hcmp (p q : BooleanNetwork (M.width t) n)
      (hp' : p∈tableNets (M.fieldRows t)) (hq' : q∈tableNets (M.fieldRows t))
      (hpd : (bitsValue (p.eval (M.encoded x t r))).toNat∣d)
      (hqd : (bitsValue (q.eval (M.encoded x t r))).toNat∣d) :
      (sameTwoVal (M.retainedComponentOrder t a m p) (M.retainedComponentOrder t a m q)).eval
        (M.encoded x t r) 0=true ↔
      padicValNat 2 (dataOrder (trueData P) (bitsValue (a.eval (M.encoded x t r))).toNat
        (d.gcd ((bitsValue (p.eval (M.encoded x t r))).toNat^n)))=
      padicValNat 2 (dataOrder (trueData P) (bitsValue (a.eval (M.encoded x t r))).toNat
        (d.gcd ((bitsValue (q.eval (M.encoded x t r))).toNat^n))) := by
    have hep:=M.retainedComponentOrder_exact hn t a m p x r hc hP hP0 hd hdiv hm (hp p hp') hpd ha
    have heq:=M.retainedComponentOrder_exact hn t a m q x r hc hP hP0 hd hdiv hm (hp q hq') hqd ha
    have hb : d ≤ 2^n:=hm ▸ (bitsValue (m.eval (M.encoded x t r))).isLt.le
    have hnp : (bitsValue ((M.retainedComponentOrder t a m p).eval (M.encoded x t r))).toNat≠0 := by
      rw [hep]
      exact data_component_order_ne_zero (by omega) hd hdiv hb (hp p hp') hpd ha
    have hnq : (bitsValue ((M.retainedComponentOrder t a m q).eval (M.encoded x t r))).toNat≠0 := by
      rw [heq]
      exact data_component_order_ne_zero (by omega) hd hdiv hb (hp q hq') hqd ha
    rw [sameTwoVal_value _ _ _ hnp hnq,hep,heq]
  constructor
  · intro h p hp' hpd q hq' hqd
    exact (hcmp p q hp' hq' hpd hqd).mp (h p hp' q hq' hpd hqd)
  · intro h p hp' q hq' hpd hqd
    exact (hcmp p q hp' hq' hpd hqd).mpr (h p hp' hpd q hq' hqd)

lemma retainedFavorable_exact {N P d : ℕ} (hn : 2 ≤ n) (t : ℕ)
    (a m : BooleanNetwork (M.width t) n) (x : Basis c) (r : Trace n t)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hd : 2 ≤ d) (hdiv : d∣P) (hm : (bitsValue (m.eval (M.encoded x t r))).toNat=d) :
    (M.retainedFavorable t a m).eval (M.encoded x t r) 0=true ↔
      dataResidueGood (trueData P) (bitsValue (a.eval (M.encoded x t r))).toNat d := by
  rw [M.retainedFavorable_table hn t a m x r hc hP hP0 hd hdiv hm]
  exact tableFavorable_correct (by omega) hd (hm ▸ (bitsValue (m.eval (M.encoded x t r))).isLt.le)
    hdiv (PhysicalTree.tableFactors_prime hc)
    (PhysicalTree.tableFactors_cover hc hP hP0 (by omega) hdiv) _

def retainedGoodList (t : ℕ) (m : BooleanNetwork (M.width t) n)
    (y : BooleanNetwork (M.width t) (n*(n^5+1))) : BooleanNetwork (M.width t) 1 :=
  any (List.ofFn (fun i : Fin (n^5)=>M.retainedFavorable t (TransitionWords.readNet y i) m))

lemma retainedGoodList_exact {N P d : ℕ} (hn : 2 ≤ n) (t : ℕ)
    (m : BooleanNetwork (M.width t) n) (y : BooleanNetwork (M.width t) (n*(n^5+1)))
    (x : Basis c) (r : Trace n t) (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hd : 2 ≤ d) (hdiv : d∣P) (hm : (bitsValue (m.eval (M.encoded x t r))).toNat=d) :
    (M.retainedGoodList t m y).eval (M.encoded x t r) 0=true ↔
      dataGoodList (trueData P) d n (y.eval (M.encoded x t r)) := by
  change (M.retainedGoodList t m y).eval (M.encoded x t r) 0=true ↔
    ∃ i : Fin (n^5),dataResidueGood (trueData P)
      (bitsValue (TransitionWords.read (y.eval (M.encoded x t r)) i)).toNat d
  rw [retainedGoodList,any_eval]
  constructor
  · rintro ⟨v,hv,he⟩
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hv
    refine ⟨i,?_⟩
    rw [M.retainedFavorable_exact hn t _ m x r hc hP hP0 hd hdiv hm,
      TransitionWords.readNet_eval] at he
    exact he
  · rintro ⟨i,hi⟩
    refine ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,?_⟩
    rw [M.retainedFavorable_exact hn t _ m x r hc hP hP0 hd hdiv hm,
      TransitionWords.readNet_eval]
    exact hi
end NodeMachine
end ExactQuantumFactoring


end

end OAI
