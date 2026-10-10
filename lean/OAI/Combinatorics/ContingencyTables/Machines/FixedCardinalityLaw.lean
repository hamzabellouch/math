import OAI.Combinatorics.ContingencyTables.Transport.FiniteDependentApproximation
import OAI.Combinatorics.ContingencyTables.Machines.FiniteFairBits
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.Field.Basic

namespace OAI

/-! # Sequential uniform sampling of a subset of prescribed size

The head is included with probability k/n; conditional on that choice,
the same rule is applied to the remaining coordinates. The exact mass
is k!(n-k)!/n!, matching the factorial factor in the companion lift.
-/

namespace ContingencyTables.FixedCardinalityLaw

open ResidualMixture FirstSuccess
open scoped BigOperators Classical
noncomputable section

def count {n : ℕ} (v : Fin n → Bool) : ℕ := ∑ i,if v i then 1 else 0

lemma count_le {n : ℕ} (v : Fin n → Bool) : count v≤n := by
  calc
    _ ≤ ∑ _i : Fin n,1 := Finset.sum_le_sum (fun i _ => by cases v i <;> simp)
    _ = n := by simp

lemma count_decompose {n : ℕ} (v : Fin (n+1) → Bool) :
    count v=(if v 0 then 1 else 0)+count (Fin.tail v) := by
  simp only [count,Fin.sum_univ_succ,Fin.tail]
  rfl

def consEquiv (n : ℕ) : ((_b : Bool) × (Fin n → Bool)) ≃ (Fin (n+1) → Bool) where
  toFun x := Fin.cons x.1 x.2
  invFun v := ⟨v 0,Fin.tail v⟩
  left_inv x := by cases x; simp
  right_inv v := Fin.cons_self_tail v

def consLaw {n : ℕ} (p : RationalLaw Bool) (Q : Bool → RationalLaw (Fin n → Bool)) :
    RationalLaw (Fin (n+1) → Bool) :=
  equivLaw (consEquiv n) (dependentJointLaw p Q)

lemma consLaw_mass {n : ℕ} (p : RationalLaw Bool) (Q : Bool → RationalLaw (Fin n → Bool))
    (v : Fin (n+1) → Bool) :
    (consLaw p Q).mass v=p.mass (v 0)*(Q (v 0)).mass (Fin.tail v) := rfl

lemma consLaw_variation {n : ℕ} (p q : RationalLaw Bool)
    (Q R : Bool → RationalLaw (Fin n → Bool)) (e : ℚ)
    (he : ∀ b,variation (Q b) (R b)≤e) :
    variation (consLaw p Q) (consLaw q R)≤variation p q+e := by
  rw [consLaw,consLaw,variation_equiv]
  exact variation_dependentJoint_uniform p q Q R e he

def bernoulli (q : ℚ) (hq0 : 0≤q) (hq1 : q≤1) : RationalLaw Bool where
  mass b := if b then q else 1-q
  nonnegative b := by cases b <;> simp [hq0,sub_nonneg.mpr hq1]
  total := by simp

def headProbability (n k : ℕ) : ℚ := ((min k (n+1):ℕ):ℚ)/(n+1)

lemma headProbability_bounds (n k : ℕ) : 0≤headProbability n k ∧ headProbability n k≤1 := by
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  · apply (div_le_one (by positivity : (0:ℚ)<n+1)).mpr
    exact_mod_cast min_le_right k (n+1)

def headLaw (n k : ℕ) : RationalLaw Bool :=
  bernoulli (headProbability n k) (headProbability_bounds n k).1 (headProbability_bounds n k).2

def remaining (n k : ℕ) (b : Bool) : ℕ := if b then k-1 else min k n

def fixedLaw : (n k : ℕ) → RationalLaw (Fin n → Bool)
  | 0, _ => pointLaw (fun i => Fin.elim0 i)
  | n+1, k => consLaw (headLaw n k) (fun b => fixedLaw n (remaining n k b))

def factorialMass (n k : ℕ) : ℚ := (k.factorial:ℚ)*((n-k).factorial:ℚ)/(n.factorial:ℚ)

private lemma factorialMass_true (n k : ℕ) (hk0 : 0<k) :
    (k:ℚ)/(n+1)*factorialMass n (k-1)=factorialMass (n+1) k := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hk0)
  simp only [factorialMass,Nat.succ_sub_succ,Nat.sub_zero,Nat.factorial_succ,
    Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.succ_eq_add_one]
  field_simp

private lemma factorialMass_false (n k : ℕ) (hk : k≤n) :
    (1-(k:ℚ)/(n+1))*factorialMass n k=factorialMass (n+1) k := by
  have hs : n+1-k=(n-k)+1 := by omega
  simp only [factorialMass,hs,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  rw [Nat.cast_sub hk]
  field_simp
  ring

/-- Each vector of the requested size has the reciprocal-binomial
mass, and all other vectors have mass zero. -/
theorem fixedLaw_mass (n k : ℕ) (hk : k≤n) (v : Fin n → Bool) :
    (fixedLaw n k).mass v=if count v=k then factorialMass n k else 0 := by
  induction n generalizing k with
  | zero =>
    have hk0 : k=0 := by omega
    subst k
    have hv : v=(fun i => Fin.elim0 i) := by funext i; exact Fin.elim0 i
    subst v
    simp [fixedLaw,pointLaw,count,factorialMass]
  | succ n ih =>
    rw [fixedLaw,consLaw_mass]
    have hcount := count_decompose v
    cases hb : v 0 with
    | false =>
      simp only [hb,Bool.false_eq_true,ite_false,zero_add] at hcount
      by_cases hkn : k≤n
      · rw [show remaining n k false=k by simp [remaining,min_eq_left hkn],ih k hkn]
        have hp : (headLaw n k).mass false=1-(k:ℚ)/(n+1) := by
          simp [headLaw,bernoulli,headProbability,min_eq_left hk]
        rw [hp]
        by_cases hc : count (Fin.tail v)=k
        · simp only [hcount,hc,ite_true]
          exact factorialMass_false n k hkn
        · simp only [hc,ite_false,mul_zero,hcount]
      · have hke : k=n+1 := by omega
        subst k
        have hp : (headLaw n (n+1)).mass false=0 := by
          simp [headLaw,bernoulli,headProbability,show (n:ℚ)+1≠0 by positivity]
        rw [hp,zero_mul]
        have hc : count v≠n+1 := by rw [hcount]; have := count_le (Fin.tail v); omega
        simp [hc]
    | true =>
      simp only [hb,ite_true] at hcount
      by_cases hk0 : k=0
      · subst k
        have hp : (headLaw n 0).mass true=0 := by simp [headLaw,bernoulli,headProbability]
        rw [hp,zero_mul]
        have hc : count v≠0 := by omega
        simp [hc]
      · have hkpos : 0<k := Nat.pos_of_ne_zero hk0
        have hr : k-1≤n := by omega
        rw [show remaining n k true=k-1 by simp [remaining],ih (k-1) hr]
        have hp : (headLaw n k).mass true=(k:ℚ)/(n+1) := by
          simp [headLaw,bernoulli,headProbability,min_eq_left hk]
        rw [hp]
        by_cases hc : count (Fin.tail v)=k-1
        · have hc' : count v=k := by omega
          simp only [hc,hc',ite_true]
          exact factorialMass_true n k hkpos
        · have hc' : count v≠k := by omega
          simp only [hc,hc',ite_false,mul_zero]

end
end ContingencyTables.FixedCardinalityLaw

end OAI
