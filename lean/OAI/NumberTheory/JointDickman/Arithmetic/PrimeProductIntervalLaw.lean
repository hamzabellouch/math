import OAI.NumberTheory.JointDickman.Arithmetic.PrimeHarmonicWeights
import OAI.NumberTheory.JointDickman.Arithmetic.RoughHarmonicLaw

namespace OAI

/-!
# The actual independent prime-product interval law

The harmonic rough counting estimate is transferred to the probability
law with an explicit, event-uniform local mass correction.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem primeProduct_interval_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) (D : ℝ) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ a b : ℝ,
        9 ≤ a → a ≤ b → b ≤ auxiliaryUpper B →
        (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log a →
        |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, primeProductMass (auxiliaryPrimes B) z n) -
          primeNormalizer (auxiliaryPrimes B) z *
            ∫ t in a..b, roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) z H (Real.log t) / t| ≤
          z ^ 2 / (auxiliaryCutoff B : ℝ) +
            K * (B : ℝ) ^ (-D) * (2 + Real.log (b / a)) := by
  obtain ⟨c, hc0, hcpos, H, K, hK, hrough⟩ := rough_harmonic_interval_law hSD hM hz D
  have hz0 : 0 ≤ z := by rcases hz with rfl | rfl <;> norm_num
  have hz1 : z ≤ 1 := by rcases hz with rfl | rfl <;> norm_num
  refine ⟨c, hc0, hcpos, H, K, hK, ?_⟩
  filter_upwards [hrough, eventually_gt_atTop 0] with B hB hB0
  intro a b ha hab hb hlog
  have hb0 : 0 ≤ b := by linarith
  have hcut : auxiliaryCutoff B ≠ 0 := by exact pow_ne_zero 1000 (Nat.ne_of_gt hB0)
  have hmass := primeProductMass_harmonic_error (U := auxiliaryUpper B) hcut hz0 hz1
    (Ioc ⌊a⌋₊ ⌊b⌋₊) (fun n hn =>
      ((by exact_mod_cast (mem_Ioc.mp hn).2 : (n : ℝ) ≤ ⌊b⌋₊).trans (Nat.floor_le hb0)).trans hb)
  have hQ := primeNormalizer_bounds (auxiliaryPrimes B) (auxiliaryPrimes_prime B) hz0 hz1
  have hweighted : |primeNormalizer (auxiliaryPrimes B) z *
      ((∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) z n / (n : ℝ)) -
        ∫ t in a..b, roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) z H (Real.log t) / t)| ≤
      K * (B : ℝ) ^ (-D) * (2 + Real.log (b / a)) := by
    rw [abs_mul, abs_of_nonneg hQ.1]
    simpa only [one_mul] using mul_le_mul hQ.2 (hB a b ha hab hlog) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have heq : (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, primeProductMass (auxiliaryPrimes B) z n) -
      primeNormalizer (auxiliaryPrimes B) z *
        (∫ t in a..b, roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) z H (Real.log t) / t) =
      ((∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, primeProductMass (auxiliaryPrimes B) z n) -
        primeNormalizer (auxiliaryPrimes B) z *
          ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) z n / (n : ℝ)) +
      primeNormalizer (auxiliaryPrimes B) z *
        ((∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) z n / (n : ℝ)) -
          ∫ t in a..b, roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) z H (Real.log t) / t) := by ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add hmass hweighted)

end JointDickman

end OAI
