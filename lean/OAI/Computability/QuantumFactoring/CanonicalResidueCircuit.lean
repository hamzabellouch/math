import Mathlib
import OAI.Computability.QuantumFactoring.TablePrimeSupport

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace BitArithmetic
attribute [local instance] Classical.propDecidable

def dividesOn {k n : ℕ} (p m : BooleanNetwork k n) : BooleanNetwork k 1 :=
  zeroWord ((m.pair p).comp (mod n))
lemma dividesOn_value {k n : ℕ} (p m : BooleanNetwork k n) (x : Basis k) :
    (dividesOn p m).eval x 0=true ↔ (bitsValue (p.eval x)).toNat∣(bitsValue (m.eval x)).toNat := by
  rw [dividesOn,zeroWord_value,eval_comp,eval_pair,mod_word,BitVec.toNat_umod,Nat.dvd_iff_mod_eq_zero]
lemma dividesOn_count {k n : ℕ} (p m : BooleanNetwork k n) :
    (dividesOn p m).net.count ≤ p.net.count+m.net.count+216*n*n+154*n+27 := by
  have hh:=zeroWord_count ((m.pair p).comp (mod n))
  have hd:=mod_count n
  simp only [count_comp,count_pair] at hh
  exact hh.trans (by omega)

def leastDivisorTest {k n : ℕ} (ps : List (BooleanNetwork k n)) (m p : BooleanNetwork k n) :
    BooleanNetwork k 1 := all (ps.map (fun q=>(dividesOn q m).bnot.bor (wordLe p q)))

lemma leastDivisorTest_value {k n : ℕ} (ps : List (BooleanNetwork k n))
    (m p : BooleanNetwork k n) (x : Basis k) :
    (leastDivisorTest ps m p).eval x 0=true ↔
      leastDivisorIn (ps.map (fun q=>(bitsValue (q.eval x)).toNat))
        (bitsValue (m.eval x)).toNat (bitsValue (p.eval x)).toNat := by
  simp only [leastDivisorTest,all_eval,List.forall_mem_map,eval_bor,Bool.or_eq_true,
    bnot_value,dividesOn_value,wordLe_eval,decide_eq_true_eq,leastDivisorIn,
    List.forall_mem_map,or_iff_not_imp_left,not_not]

lemma leastDivisorTest_count {k n c : ℕ} (ps : List (BooleanNetwork k n))
    (m p : BooleanNetwork k n) (hps : ∀ q∈ps,q.net.count≤c)
    (hm : m.net.count≤c) (hp : p.net.count≤c) :
    (leastDivisorTest ps m p).net.count≤ps.length*(4*c+216*n*n+202*n+42)+1 := by
  have hh:=all_count (ps.map (fun q=>(dividesOn q m).bnot.bor (wordLe p q)))
    (c:=4*c+216*n*n+202*n+41) (by
      intro b hb
      obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hb
      have hd:=dividesOn_count q m
      have hl:=wordLe_count p q
      have hqc:=hps q hq
      simp only [count_bor,count_bnot]
      omega)
  change (all (ps.map (fun q=>(dividesOn q m).bnot.bor (wordLe p q)))).net.count ≤ _
  simp only [List.length_map] at hh
  omega

def componentCongruence {k n : ℕ} (ps : List (BooleanNetwork k n))
    (a m p : BooleanNetwork k n) : BooleanNetwork k 1 :=
  let q:=primeComponent m p
  equalOn ((a.pair q).comp (mod n)) (wordMux (leastDivisorTest ps m p)
    (wordConstant (BitVec.ofNat n 1)) (natSubOn q (wordConstant (BitVec.ofNat n 1))))

lemma componentCongruence_value {k n : ℕ} (ps : List (BooleanNetwork k n))
    (a m p : BooleanNetwork k n) (x : Basis k)
    (hm : 2≤(bitsValue (m.eval x)).toNat) (hp : ((bitsValue (p.eval x)).toNat).Prime) :
    (componentCongruence ps a m p).eval x 0=true ↔
      (bitsValue (a.eval x)).toNat % Nat.gcd (bitsValue (m.eval x)).toNat
        ((bitsValue (p.eval x)).toNat^n)=
      if leastDivisorIn (ps.map (fun q=>(bitsValue (q.eval x)).toNat))
        (bitsValue (m.eval x)).toNat (bitsValue (p.eval x)).toNat
      then 1 else Nat.gcd (bitsValue (m.eval x)).toNat ((bitsValue (p.eval x)).toNat^n)-1 := by
  have h1 : 1<2^n := by have hh:=(bitsValue (m.eval x)).isLt;omega
  have hq : (bitsValue ((primeComponent m p).eval x)).toNat=
      Nat.gcd (bitsValue (m.eval x)).toNat ((bitsValue (p.eval x)).toNat^n) := by
    rw [primeComponent_value m p x (by omega) hp,
      prime_component_gcd (by omega) hp (bitsValue (m.eval x)).isLt.le]
  rw [componentCongruence,equalOn_value,eval_comp,eval_pair,mod_word,BitVec.toNat_umod,hq,wordMux_eval]
  by_cases ht : (leastDivisorTest ps m p).eval x 0=true
  · rw [ite_eq_left ht,ite_eq_left ((leastDivisorTest_value ps m p x).mp ht),wordConstant_eval,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt h1]
  · rw [ite_eq_right ht,ite_eq_right (fun h=>ht ((leastDivisorTest_value ps m p x).mpr h)),natSubOn_value,
      hq,wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h1]

def tableCanonicalNet {k n : ℕ} (ps : List (BooleanNetwork k n))
    (a m : BooleanNetwork k n) : BooleanNetwork k 1 :=
  (wordLt a m).band (all (ps.map (fun p=>(dividesOn p m).bnot.bor (componentCongruence ps a m p))))

lemma tableCanonicalNet_value {k n : ℕ} (ps : List (BooleanNetwork k n))
    (a m : BooleanNetwork k n) (x : Basis k)
    (hm : 2≤(bitsValue (m.eval x)).toNat)
    (hps : ∀ p∈ps,((bitsValue (p.eval x)).toNat).Prime) :
    (tableCanonicalNet ps a m).eval x 0=true ↔
      tableCanonical (ps.map (fun p=>(bitsValue (p.eval x)).toNat))
        (bitsValue (a.eval x)).toNat (bitsValue (m.eval x)).toNat n := by
  rw [tableCanonicalNet,eval_band,Bool.and_eq_true,wordLt_eval,decide_eq_true_eq,tableCanonical]
  apply and_congr_right
  intro _
  simp only [all_eval,List.forall_mem_map,eval_bor,Bool.or_eq_true,bnot_value,dividesOn_value]
  constructor
  · intro h p hp hpd
    exact (componentCongruence_value ps a m p x hm (hps p hp)).mp ((h p hp).resolve_left (not_not.mpr hpd))
  · intro h p hp
    by_cases hpd : (bitsValue (p.eval x)).toNat∣(bitsValue (m.eval x)).toNat
    · exact Or.inr ((componentCongruence_value ps a m p x hm (hps p hp)).mpr
        (h p hp hpd))
    · exact Or.inl hpd
def componentCongruenceBound (n l c : ℕ) : ℕ :=
  c+3*primeComponentBound n c+216*n*n+500*n+100+
    l*(4*c+216*n*n+202*n+42)

lemma componentCongruence_count {k n c : ℕ} (ps : List (BooleanNetwork k n))
    (a m p : BooleanNetwork k n) (hps : ∀ q∈ps,q.net.count≤c)
    (ha : a.net.count≤c) (hm : m.net.count≤c) (hp : p.net.count≤c) :
    (componentCongruence ps a m p).net.count≤componentCongruenceBound n ps.length c := by
  have hq:=primeComponent_count m p hm hp
  have hl:=leastDivisorTest_count ps m p hps hm hp
  have he:=equalOn_count ((a.pair (primeComponent m p)).comp (mod n))
    (wordMux (leastDivisorTest ps m p) (wordConstant (BitVec.ofNat n 1))
      (natSubOn (primeComponent m p) (wordConstant (BitVec.ofNat n 1))))
  have hs:=natSubOn_count (primeComponent m p) (wordConstant (BitVec.ofNat n 1))
  have hd:=mod_count n
  simp only [count_comp,count_pair,wordMux_count,wordConstant_count] at he hs
  change (equalOn _ _).net.count≤_
  dsimp only [componentCongruenceBound]
  omega

def tableCanonicalBound (n l c : ℕ) : ℕ :=
  2*c+48*n+10+l*(2*c+216*n*n+154*n+33+componentCongruenceBound n l c)+2

lemma tableCanonicalNet_count {k n c : ℕ} (ps : List (BooleanNetwork k n))
    (a m : BooleanNetwork k n) (hps : ∀ q∈ps,q.net.count≤c)
    (ha : a.net.count≤c) (hm : m.net.count≤c) :
    (tableCanonicalNet ps a m).net.count≤tableCanonicalBound n ps.length c := by
  have hl:=wordLt_count a m
  have hall:=all_count (ps.map (fun p=>(dividesOn p m).bnot.bor (componentCongruence ps a m p)))
    (c:=2*c+216*n*n+154*n+32+componentCongruenceBound n ps.length c) (by
      intro b hb
      obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hb
      have hc:=componentCongruence_count ps a m p hps ha hm (hps p hp)
      have hd:=dividesOn_count p m
      have hp':=hps p hp
      simp only [count_bor,count_bnot]
      omega)
  simp only [List.length_map] at hall
  have hr : 2*c+216*n*n+154*n+32+componentCongruenceBound n ps.length c+1 =
      2*c+216*n*n+154*n+33+componentCongruenceBound n ps.length c := by omega
  rw [hr] at hall
  simp only [tableCanonicalNet,count_band,tableCanonicalBound]
  omega
end BitArithmetic
end ExactQuantumFactoring


end

end OAI
