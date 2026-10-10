import Mathlib
import OAI.Computability.QuantumFactoring.ComponentPhiCircuit
import OAI.Computability.QuantumFactoring.DistinctProductCircuit

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

lemma equalLevelSum_le_totient {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) (ho : Odd m) :
    (∑ t : Fin (n+1),∏ p : Component m,
      closedLevelCount (primePowerUnitCount p.val (m.factorization p.val)) t.val)≤ m.totient := by
  classical
  let p₀ : Component m := ⟨m.minFac,Nat.mem_primeFactors.mpr
    ⟨Nat.minFac_prime (by omega),Nat.minFac_dvd m,by omega⟩⟩
  have h0 : m≠0:=by omega
  let : NeZero m:=⟨h0⟩
  rw [←equal_component_card h0 hb ho p₀]
  calc
    _≤Fintype.card (∀ p : Component m,ComponentUnits m p):=Fintype.card_subtype_le _
    _=Fintype.card (ZMod m)ˣ:=(Fintype.card_congr (unitCRT m h0).toEquiv).symm
    _=m.totient:=ZMod.card_units_eq_totient m

lemma componentLevelProduct_lt {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) (ho : Odd m)
    (t : Fin (n+1)) :
    (∏ p : Component m,closedLevelCount (primePowerUnitCount p.val (m.factorization p.val)) t.val)<2^n := by
  have hs:=Finset.single_le_sum (f:=fun t : Fin (n+1)=>∏ p : Component m,
    closedLevelCount (primePowerUnitCount p.val (m.factorization p.val)) t.val)
    (fun _ _=>Nat.zero_le _) (Finset.mem_univ t)
  exact (hs.trans (equalLevelSum_le_totient hm hb ho)).trans_lt ((Nat.totient_le m).trans_lt hb)

lemma table_level_product {ps : List ℕ} {m : ℕ} (hm : m≠0)
    (hp : ∀ p∈ps,p.Prime) (hcover : ∀ p : ℕ,p.Prime→p∣m→p∈ps) (t : ℕ) :
    (∏ p∈ps.toFinset,if p∣m then closedLevelCount (primePowerUnitCount p (m.factorization p)) t else 1)=
      ∏ p : Component m,closedLevelCount (primePowerUnitCount p.val (m.factorization p.val)) t := by
  classical
  have he : ps.toFinset.filter (fun p=>p∣m)=m.primeFactors := by
    ext p
    simp only [Finset.mem_filter,List.mem_toFinset]
    constructor
    · rintro ⟨hps,hpd⟩
      exact Nat.mem_primeFactors.mpr ⟨hp p hps,hpd,hm⟩
    · intro h
      obtain ⟨hpp,hpd,_⟩:=Nat.mem_primeFactors.mp h
      exact ⟨hcover p hpp hpd,hpd⟩
  rw [←Finset.prod_filter,he]
  exact (Finset.prod_coe_sort _ _).symm

namespace BitArithmetic

def tableLevelNet {k n : ℕ} (m : BooleanNetwork k n) (ps : List (BooleanNetwork k n)) (t : ℕ) :
    BooleanNetwork k n := distinctProductNet (fun p=>componentLevelNet m p t) ps

lemma tableLevelNet_value {k n : ℕ} (hn : 2 ≤ n) (m : BooleanNetwork k n)
    (ps : List (BooleanNetwork k n)) (x : Basis k) (hm : 2≤(bitsValue (m.eval x)).toNat)
    (ho : Odd (bitsValue (m.eval x)).toNat)
    (hp : ∀ p∈ps,((bitsValue (p.eval x)).toNat).Prime)
    (hcover : ∀ p : ℕ,p.Prime→p∣(bitsValue (m.eval x)).toNat→
      p∈ps.map (fun q=>(bitsValue (q.eval x)).toNat)) (t : Fin (n+1)) :
    (bitsValue ((tableLevelNet m ps t.val).eval x)).toNat=
      ∏ p : Component (bitsValue (m.eval x)).toNat,
        closedLevelCount (primePowerUnitCount p.val ((bitsValue (m.eval x)).toNat.factorization p.val)) t.val := by
  let f : ℕ→ℕ:=fun p=>if p∣(bitsValue (m.eval x)).toNat then
    closedLevelCount (primePowerUnitCount p ((bitsValue (m.eval x)).toNat.factorization p)) t.val else 1
  have hh:=distinctProductNet_value (fun p=>componentLevelNet m p t.val) ps x f (by
    intro p hp'
    have he:=componentLevelNet_value hn m p x (by omega) (hp p hp') t.val
    change (bitsValue ((componentLevelNet m p t.val).eval x)).toNat=f (bitsValue (p.eval x)).toNat at he
    rw [←he,Nat.mod_eq_of_lt (bitsValue ((componentLevelNet m p t.val).eval x)).isLt])
  rw [tableLevelNet,hh]
  dsimp only [f]
  rw [table_level_product (by omega) (by
    intro p hp'
    obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp'
    exact hp q hq) hcover t.val]
  exact Nat.mod_eq_of_lt (componentLevelProduct_lt hm (bitsValue (m.eval x)).isLt ho t)

lemma tableLevelNet_count {k n c : ℕ} (m : BooleanNetwork k n)
    (ps : List (BooleanNetwork k n)) (hm : m.net.count≤c)
    (hp : ∀ p∈ps,p.net.count≤c) (t : ℕ) :
    (tableLevelNet m ps t).net.count≤
      ps.length*(componentLevelBound n c+90*n*n+22*n+7+ps.length*(2*c+96*n+25))+n := by
  exact distinctProductNet_count _ _ hp (fun p hh=>componentLevelNet_count m p hm (hp p hh) t)
end BitArithmetic
end ExactQuantumFactoring


end

end OAI
