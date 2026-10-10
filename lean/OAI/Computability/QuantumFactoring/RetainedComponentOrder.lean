import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalDataLog
import OAI.Computability.QuantumFactoring.PrimeComponentCircuit
import OAI.Computability.QuantumFactoring.RetrospectiveStatistics
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

def retainedComponentOrder (t : ℕ) (a m p : BooleanNetwork (M.width t) n) : BooleanNetwork (M.width t) n :=
  M.retainedOrder t a (primeComponent m p)

lemma retainedComponentOrder_exact {N P d : ℕ} (hn : 2≤n) (t : ℕ)
    (a m p : BooleanNetwork (M.width t) n) (x : Basis c) (r : Trace n t)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hd : 2≤d) (hdiv : d∣P) (hm : (bitsValue (m.eval (M.encoded x t r))).toNat=d)
    (hp : ((bitsValue (p.eval (M.encoded x t r))).toNat).Prime)
    (hpd : (bitsValue (p.eval (M.encoded x t r))).toNat∣d)
    (ha : ((bitsValue (a.eval (M.encoded x t r))).toNat).Coprime d) :
    (bitsValue ((M.retainedComponentOrder t a m p).eval (M.encoded x t r))).toNat=
      dataOrder (trueData P) (bitsValue (a.eval (M.encoded x t r))).toNat
        (Nat.gcd d ((bitsValue (p.eval (M.encoded x t r))).toNat^n)) := by
  let z:=M.encoded x t r
  let pN:=(bitsValue (p.eval z)).toNat
  let q:=pN^(d.factorization pN)
  have hq : 2≤q := hp.two_le.trans (Nat.le_pow (hp.factorization_pos_of_dvd (by omega) hpd))
  have hqd : q∣d := Nat.ordProj_dvd d pN
  have hqa : ((bitsValue (a.eval z)).toNat).Coprime q := ha.of_dvd_right hqd
  have hu : IsUnit ((bitsValue (a.eval z)).toNat : ZMod q) := (ZMod.isUnit_iff_coprime _ _).mpr hqa
  have he : (bitsValue ((primeComponent m p).eval z)).toNat=q := by
    rw [primeComponent_value m p z (by change (bitsValue (m.eval (M.encoded x t r))).toNat≠0;omega) hp,hm]
  have ho:=M.retainedOrder_exact hn t a (primeComponent m p) x r hc hP hP0 hq
    (hqd.trans hdiv) hu.unit hu.unit_spec.symm he
  have ht:=dataOrder_correct (by omega : 0<P) hq (hqd.trans hdiv) hu.unit hu.unit_spec.symm
  dsimp only [retainedComponentOrder]
  rw [ho,prime_component_gcd (by omega) hp (hm ▸ (bitsValue (m.eval z)).isLt.le)]
  exact ht.symm

lemma data_component_order_ne_zero {P d a p n : ℕ} (hP : 0<P) (hd : 2≤d)
    (hdiv : d∣P) (hb : d≤2^n) (hp : p.Prime) (hpd : p∣d) (ha : a.Coprime d) :
    dataOrder (trueData P) a (Nat.gcd d (p^n))≠0 := by
  rw [prime_component_gcd (by omega) hp hb]
  let q:=p^(d.factorization p)
  have hq : 2≤q:=hp.two_le.trans (Nat.le_pow (hp.factorization_pos_of_dvd (by omega) hpd))
  have hqd : q∣d:=Nat.ordProj_dvd d p
  have hqa : a.Coprime q:=ha.of_dvd_right hqd
  let : NeZero q:=⟨by omega⟩
  have hu : IsUnit (a : ZMod q):=(ZMod.isUnit_iff_coprime _ _).mpr hqa
  rw [dataOrder_correct hP hq (hqd.trans hdiv) hu.unit hu.unit_spec.symm]
  exact Nat.ne_of_gt (orderOf_pos _)
end NodeMachine
end ExactQuantumFactoring


end

end OAI
