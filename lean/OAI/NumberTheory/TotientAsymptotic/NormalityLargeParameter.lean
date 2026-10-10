import OAI.NumberTheory.TotientAsymptotic.PublishedNormality
import OAI.NumberTheory.TotientAsymptotic.ResidualFactorCount

namespace OAI

/-! The terminal parameter range: all primes are normal once log S exceeds the endpoint. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

lemma omegaIn_le_length (n : ℕ) (U T : ℝ) :
    omegaIn n U T ≤ n.primeFactorsList.length := List.length_filter_le _ _

lemma normalPrime_of_log_parameter {S : ℝ} (hS : 2 < S) {n p : ℕ}
    (hn : 1 ≤ n) (hp : p.Prime) (hpn : p ≤ n) (hlarge : (n:ℝ) ≤ Real.log S) :
    IsNormalPrime S p := by
  have hSpos : 0 < S := by linarith
  have hNpos : (0:ℝ) < n := by exact_mod_cast hn
  have hlogN : Real.log n ≤ B S := Real.log_le_log hNpos hlarge
  have hpm : 0 < p-1 := by have := hp.two_le; omega
  have hlogp : Real.log (p-1:ℕ) ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast hpm) (by exact_mod_cast (show p-1 ≤ n by omega))
  refine ⟨hp,?_,?_⟩
  · have hΩ : (omegaIn (p-1) 1 S:ℝ) ≤ (p-1).primeFactorsList.length := by
      exact_mod_cast omegaIn_le_length (p-1) 1 S
    have hh := omega_count_le_log hpm
    linarith
  · intro U T hSU hUT hT
    have he : (n:ℝ)+1 ≤ S := by
      calc
        _ ≤ Real.exp (n:ℝ) := Real.add_one_le_exp _
        _ ≤ Real.exp (Real.log S) := Real.exp_le_exp.mpr hlarge
        _ = S := Real.exp_log hSpos
    have hpmN : (p-1:ℕ) ≤ n := by omega
    have hpmR : ((p-1:ℕ):ℝ) ≤ n := by exact_mod_cast hpmN
    linarith

theorem nonNormalPrimes_empty_of_large_parameter {S : ℝ} (hS : 2 < S) {n : ℕ}
    (hn : 1 ≤ n) (hlarge : (n:ℝ) ≤ Real.log S) : nonNormalPrimes S n = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hpN,hbad⟩ := Finset.mem_filter.mp hp
  obtain ⟨hle,hprime⟩ := Nat.mem_primesLE.mp hpN
  exact hbad (normalPrime_of_log_parameter hS hn hprime hle hlarge)

end TotientAsymptotic

end

end OAI
