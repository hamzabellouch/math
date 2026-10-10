import Mathlib
import OAI.Computability.QuantumFactoring.TableLevelCircuit
import OAI.Computability.QuantumFactoring.TableDirectPhi
import OAI.Computability.QuantumFactoring.WordSumCircuit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
open scoped BigOperators
namespace BitArithmetic

def tableBadCountNet {k n : ℕ} (m : BooleanNetwork k n) (ps : List (BooleanNetwork k n)) :
    BooleanNetwork k n := sumNet (List.ofFn (fun t : Fin (n+1)=>tableLevelNet m ps t.val))

lemma tableBadCountNet_value {k n : ℕ} (hn : 2 ≤ n) (m : BooleanNetwork k n)
    (ps : List (BooleanNetwork k n)) (x : Basis k) (hm : 2≤(bitsValue (m.eval x)).toNat)
    (ho : Odd (bitsValue (m.eval x)).toNat)
    (hp : ∀ p∈ps,((bitsValue (p.eval x)).toNat).Prime)
    (hcover : ∀ p : ℕ,p.Prime→p∣(bitsValue (m.eval x)).toNat→
      p∈ps.map (fun q=>(bitsValue (q.eval x)).toNat)) :
    (bitsValue ((tableBadCountNet m ps).eval x)).toNat=
      ∑ t : Fin (n+1),∏ p : Component (bitsValue (m.eval x)).toNat,
        closedLevelCount (primePowerUnitCount p.val ((bitsValue (m.eval x)).toNat.factorization p.val)) t.val := by
  have hs:=equalLevelSum_le_totient hm (bitsValue (m.eval x)).isLt ho
  rw [tableBadCountNet,sumNet_nat,List.map_ofFn,List.sum_ofFn]
  have he : (fun t : Fin (n+1)=>(bitsValue ((tableLevelNet m ps t.val).eval x)).toNat)=
      (fun t : Fin (n+1)=>∏ p : Component (bitsValue (m.eval x)).toNat,
        closedLevelCount (primePowerUnitCount p.val ((bitsValue (m.eval x)).toNat.factorization p.val)) t.val) := by
    funext t
    exact tableLevelNet_value hn m ps x hm ho hp hcover t
  change (∑ t : Fin (n+1),(bitsValue ((tableLevelNet m ps t.val).eval x)).toNat)%2^n=_
  rw [he,Nat.mod_eq_of_lt (hs.trans_lt ((Nat.totient_le _).trans_lt (bitsValue (m.eval x)).isLt))]

/-- The exact source F, computed from supplied prime rows using polynomial
integer circuits. Distinctness tests remove repeated table entries. -/
def tableFavorableCountNet {k n : ℕ} (m : BooleanNetwork k n) (ps : List (BooleanNetwork k n)) :
    BooleanNetwork k n := natSubOn (primesPhiNet m ps) (tableBadCountNet m ps)

lemma tableFavorableCountNet_value {k n : ℕ} (hn : 2 ≤ n) (m : BooleanNetwork k n)
    (ps : List (BooleanNetwork k n)) (x : Basis k) (hm : 2≤(bitsValue (m.eval x)).toNat)
    (ho : Odd (bitsValue (m.eval x)).toNat)
    (hp : ∀ p∈ps,((bitsValue (p.eval x)).toNat).Prime)
    (hcover : ∀ p : ℕ,p.Prime→p∣(bitsValue (m.eval x)).toNat→
      p∈ps.map (fun q=>(bitsValue (q.eval x)).toNat)) :
    (bitsValue ((tableFavorableCountNet m ps).eval x)).toNat=
      favorableCount (bitsValue (m.eval x)).toNat n := by
  rw [tableFavorableCountNet,natSubOn_value,primesPhiNet_value (by omega) m ps x (by omega) hp hcover,
    tableBadCountNet_value hn m ps x hm ho hp hcover]
  rfl

def tableBadCountBound (n f c : ℕ) : ℕ :=
  (n+1)*(f*(componentLevelBound n c+90*n*n+22*n+7+f*(2*c+96*n+25))+n+86*n+6)+n

lemma tableBadCountNet_count {k n c : ℕ} (m : BooleanNetwork k n)
    (ps : List (BooleanNetwork k n)) (hm : m.net.count≤c) (hp : ∀ p∈ps,p.net.count≤c) :
    (tableBadCountNet m ps).net.count≤tableBadCountBound n ps.length c := by
  have hh:=sumNet_count (List.ofFn (fun t : Fin (n+1)=>tableLevelNet m ps t.val)) (by
    intro q hq
    obtain ⟨t,rfl⟩:=List.mem_ofFn.mp hq
    exact tableLevelNet_count m ps hm hp t.val)
  simpa only [tableBadCountNet,tableBadCountBound,List.length_ofFn] using hh

def tableFavorableCountBound (n f c : ℕ) : ℕ :=
  2*(c+n+(n*f)*totientStepBound n c)+2*tableBadCountBound n f c+214*n+15

lemma tableFavorableCountNet_count {k n c : ℕ} (m : BooleanNetwork k n)
    (ps : List (BooleanNetwork k n)) (hm : m.net.count≤c) (hp : ∀ p∈ps,p.net.count≤c) :
    (tableFavorableCountNet m ps).net.count≤tableFavorableCountBound n ps.length c := by
  have hphi:=primesPhiNet_count m ps hm hp
  have hbad:=tableBadCountNet_count m ps hm hp
  have hs:=natSubOn_count (primesPhiNet m ps) (tableBadCountNet m ps)
  change (natSubOn _ _).net.count≤_
  dsimp only [tableFavorableCountBound]
  omega
end BitArithmetic
end ExactQuantumFactoring


end

end OAI
