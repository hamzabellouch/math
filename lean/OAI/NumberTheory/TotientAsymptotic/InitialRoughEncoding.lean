import OAI.NumberTheory.TotientAsymptotic.FordBandSupports
import OAI.NumberTheory.TotientAsymptotic.SquarefreeRoughMass

namespace OAI

/-! Extracting the largest prime in the first, large rough factor. -/
noncomputable section
namespace TotientAsymptotic

structure InitialRoughConditions (a b d : ℕ) (y U : ℝ) (n : ℕ) : Prop where
  squarefree : Squarefree n
  large : Real.sqrt y < n
  size : ((d*n:ℕ):ℝ) ≤ y
  left_prime : (a*n+1).Prime
  right_prime : (b*n+1).Prime
  different : a*n+1 ≠ b*n+1
  left_le : ((a*n:ℕ):ℝ) ≤ y
  right_le : ((b*n:ℕ):ℝ) ≤ y
  omega_le : (n.primeFactorsList.length:ℝ) ≤ 3*B y
  support : ∀ p ∈ n.primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ y

def initialRoughEncoding (n : ℕ) : ℕ × ℕ := (n/largestPrimeFactor n,largestPrimeFactor n)

lemma initial_rough_two {a b d : ℕ} {y U : ℝ} {n : ℕ}
    (hy : Real.exp 2 ≤ y) (hn : InitialRoughConditions a b d y U n) : 2 ≤ n := by
  have hye : 1 ≤ y := by have := Real.add_one_le_exp (2:ℝ); linarith
  have hs : 1 ≤ Real.sqrt y := Real.one_le_sqrt.mpr hye
  have hnr : (1:ℝ) < n := hs.trans_lt hn.large
  exact_mod_cast hnr

lemma initial_rough_log_largest {a b d : ℕ} {y U : ℝ} {n : ℕ}
    (hy : Real.exp 2 ≤ y) (hBy : 1 ≤ B y) (hn : InitialRoughConditions a b d y U n) :
    Real.log y/(6*B y) ≤ Real.log (largestPrimeFactor n) := by
  have hn2 := initial_rough_two hy hn
  have hn0 : 0 < n := by omega
  have hy0 : 0 < y := (Real.exp_pos 2).trans_le hy
  have hl := smooth_integer_log_bound hn0
    (show (1:ℝ) ≤ largestPrimeFactor n by
      exact_mod_cast (show 1 ≤ largestPrimeFactor n from le_max_left _ _))
    le_rfl hn.omega_le
  have hln := Real.log_lt_log (Real.sqrt_pos.mpr hy0) hn.large
  rw [Real.log_sqrt hy0.le] at hln
  apply (div_le_iff₀ (by positivity : 0 < 6*B y)).mpr
  nlinarith

lemma initial_rough_product {a b d : ℕ} {y U : ℝ} {n : ℕ}
    (hy : Real.exp 2 ≤ y) (hn : InitialRoughConditions a b d y U n) :
    (initialRoughEncoding n).1*(initialRoughEncoding n).2=n := by
  exact Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors (largestPrimeFactor_mem (initial_rough_two hy hn)))

lemma initial_rough_injOn {a b d : ℕ} {y U : ℝ} (hy : Real.exp 2 ≤ y) (Q : Finset ℕ)
    (hQ : ∀ n ∈ Q,InitialRoughConditions a b d y U n) :
    Set.InjOn initialRoughEncoding (↑Q : Set ℕ) := by
  intro n hn m hm he
  have hh := congrArg (fun z : ℕ × ℕ => z.1*z.2) he
  rwa [initial_rough_product hy (hQ n hn),initial_rough_product hy (hQ m hm)] at hh

lemma initial_rough_residual {a b d : ℕ} {y U : ℝ} {n : ℕ}
    (hy : Real.exp 2 ≤ y) (hn : InitialRoughConditions a b d y U n) :
    0 < (initialRoughEncoding n).1 ∧ (initialRoughEncoding n).2.Prime ∧
    Squarefree (initialRoughEncoding n).1 ∧
    ∀ p ∈ (initialRoughEncoding n).1.primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ y := by
  have hn2 := initial_rough_two hy hn
  have hn0 : 0 < n := by omega
  have hq := Nat.prime_of_mem_primeFactors (largestPrimeFactor_mem hn2)
  have hqd := Nat.dvd_of_mem_primeFactors (largestPrimeFactor_mem hn2)
  have hd : (initialRoughEncoding n).1 ∣ n := Nat.div_dvd_of_dvd hqd
  refine ⟨Nat.div_pos (Nat.le_of_dvd hn0 hqd) hq.pos,hq,
    Squarefree.squarefree_of_dvd hd hn.squarefree,?_⟩
  intro p hp
  exact hn.support p (Nat.primeFactorsList_subset_of_dvd hd hn0.ne' hp)

end TotientAsymptotic

end

end OAI
