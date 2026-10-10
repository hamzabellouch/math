import Mathlib
import OAI.Computability.QuantumFactoring.FactorVerifierBounds
import OAI.Computability.QuantumFactoring.GcdCircuit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork

lemma prime_component_gcd {m p n : ℕ} (hm : m≠0) (hp : p.Prime) (hb : m≤2^n) :
    Nat.gcd m (p^n)=p^(m.factorization p) := by
  have he : m.factorization p≤n :=
    Nat.factorization_le_of_le_pow (hb.trans (Nat.pow_le_pow_left hp.two_le n))
  apply Nat.eq_of_factorization_eq (Nat.gcd_ne_zero_left hm) (pow_ne_zero _ hp.ne_zero)
  intro q
  rw [Nat.factorization_gcd hm (pow_ne_zero _ hp.ne_zero),hp.factorization_pow,
    hp.factorization_pow,Finsupp.inf_apply]
  by_cases h : q=p
  · subst q
    simp only [Finsupp.single_eq_same]
    exact min_eq_left he
  · simp only [Finsupp.single_eq_of_ne h,Nat.min_zero]

namespace BitArithmetic
/-- A polynomial-width, polynomial-size component modulus circuit. It uses
p as an input prime, not an oracle or enumeration of prime factors of m. -/
def componentWidth (n : ℕ) : ℕ := n*n+1

def primeComponent {k n : ℕ} (m p : BooleanNetwork k n) : BooleanNetwork k n :=
  let w:=componentWidth n
  let mw:=m.comp (resizeWord n w)
  let pw:=p.comp (resizeWord n w)
  ((mw.pair (productNet (List.replicate n pw))).comp (gcdNet w)).comp (resizeWord w n)

lemma primeComponent_value {k n : ℕ} (m p : BooleanNetwork k n) (x : Basis k)
    (hm : (bitsValue (m.eval x)).toNat≠0) (hp : ((bitsValue (p.eval x)).toNat).Prime) :
    (bitsValue ((primeComponent m p).eval x)).toNat=
      (bitsValue (p.eval x)).toNat^((bitsValue (m.eval x)).toNat.factorization
        (bitsValue (p.eval x)).toNat) := by
  have hn : n≤componentWidth n := by dsimp only [componentWidth];nlinarith
  have hpB : (bitsValue (p.eval x)).toNat^n<2^(componentWidth n) := by
    have h₁ := Nat.pow_le_pow_left (bitsValue (p.eval x)).isLt.le n
    rw [←pow_mul] at h₁
    exact h₁.trans_lt (by rw [componentWidth,pow_succ];have := Nat.two_pow_pos (n*n);omega)
  have hh : (bitsValue ((productNet (List.replicate n
      (p.comp (resizeWord n (componentWidth n))))).eval x)).toNat=(bitsValue (p.eval x)).toNat^n := by
    rw [productNet_nat,List.map_replicate,List.prod_replicate,eval_comp,resizeWord_toNat hn,
      Nat.mod_eq_of_lt hpB]
  rw [primeComponent,eval_comp,resizeWord_value,BitVec.toNat_setWidth,eval_comp,
    eval_pair,gcdNet_value,eval_comp,resizeWord_toNat hn,hh]
  rw [prime_component_gcd hm hp (bitsValue (m.eval x)).isLt.le]
  exact Nat.mod_eq_of_lt ((Nat.le_of_dvd (Nat.pos_of_ne_zero hm)
    (Nat.ordProj_dvd _ _)).trans_lt (bitsValue (m.eval x)).isLt)

def primeComponentBound (n c : ℕ) : ℕ :=
  let w:=componentWidth n
  c+w+(w+n*(c+w+90*w*w+14*w+6))+2*w*(216*w*w+300*w+100)+n

lemma primeComponent_count {k n c : ℕ} (m p : BooleanNetwork k n)
    (hm : m.net.count≤c) (hp : p.net.count≤c) :
    (primeComponent m p).net.count≤primeComponentBound n c := by
  have hr:=resizeWord_count n (componentWidth n)
  have hr':=resizeWord_count (componentWidth n) n
  have hprod:=productNet_count (List.replicate n (p.comp (resizeWord n (componentWidth n))))
    (c:=c+componentWidth n) (by
      intro q hq
      have he:=(List.mem_replicate.mp hq).2
      subst q
      rw [count_comp]
      omega)
  have hg:=gcdNet_count (componentWidth n)
  simp only [List.length_replicate] at hprod
  simp only [primeComponent,count_comp,count_pair]
  dsimp only [primeComponentBound]
  omega
end BitArithmetic
end ExactQuantumFactoring


end

end OAI
