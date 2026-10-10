import OAI.NumberTheory.JointDickman.Arithmetic.RoughResidueHarmonic
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeProductIntervalLaw

namespace OAI

/-! # Prime-product interval probabilities with a unit residue restriction -/

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
theorem sum_roughResidueWeight_div {q : ℕ} (S : Finset ℕ) (r : ZMod q)
    (E : Finset ℕ) (z : ℝ) :
    (∑ n ∈ S.filter (fun (n : ℕ) => (n : ZMod q) = r), roughSquarefreeWeight E z n / (n : ℝ)) =
      ∑ n ∈ S, roughResidueWeight r E z n / (n : ℝ) := by
  rw [sum_filter]
  apply sum_congr rfl
  intro n _
  by_cases h : (n : ZMod q) = r <;> simp [roughResidueWeight, h]

open Classical in
theorem primeProduct_residue_interval_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z D : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) (hD : 0 ≤ D) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ a b : ℝ,
        9 ≤ a → a ≤ b → b ≤ auxiliaryUpper B →
        (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log a →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
        ∀ r : (ZMod q)ˣ,
        |(∑ n ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun (n : ℕ) => (n : ZMod q) = (r : ZMod q)),
            primeProductMass (auxiliaryPrimes B) z n) -
          primeNormalizer (auxiliaryPrimes B) z *
            (∫ t in a..b, roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) z H
              (Real.log t) / t) / q.totient| ≤
          z ^ 2 / (auxiliaryCutoff B : ℝ) +
            K * (B : ℝ) ^ (-D) * (2 + Real.log (b / a)) := by
  obtain ⟨c, hc0, hcpos, H, K, hK, hrough⟩ := rough_residue_harmonic_interval_law hSD hSW hM hz hD
  have hz0 : 0 ≤ z := by rcases hz with rfl | rfl <;> norm_num
  have hz1 : z ≤ 1 := by rcases hz with rfl | rfl <;> norm_num
  refine ⟨c, hc0, hcpos, H, K, hK, ?_⟩
  filter_upwards [hrough, eventually_gt_atTop 0] with B hB hB0
  intro a b ha hab hb hlog q _ hq r
  have hb0 : 0 ≤ b := by linarith
  have hcut : auxiliaryCutoff B ≠ 0 := pow_ne_zero 1000 (Nat.ne_of_gt hB0)
  have hmass := primeProductMass_harmonic_error (U := auxiliaryUpper B) hcut hz0 hz1
    ((Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun n => (n : ZMod q) = (r : ZMod q))) (fun n hn =>
      ((by exact_mod_cast (mem_Ioc.mp (mem_filter.mp hn).1).2 : (n : ℝ) ≤ ⌊b⌋₊).trans
        (Nat.floor_le hb0)).trans hb)
  rw [sum_roughResidueWeight_div] at hmass
  have hQ := primeNormalizer_bounds (auxiliaryPrimes B) (auxiliaryPrimes_prime B) hz0 hz1
  have hweighted : |primeNormalizer (auxiliaryPrimes B) z *
      ((∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊,
          roughResidueWeight (r : ZMod q) (Nat.primesLE (auxiliaryCutoff B)) z n / (n : ℝ)) -
        (∫ t in a..b, roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) z H
          (Real.log t) / t) / q.totient)| ≤
      K * (B : ℝ) ^ (-D) * (2 + Real.log (b / a)) := by
    rw [abs_mul, abs_of_nonneg hQ.1]
    simpa only [one_mul] using mul_le_mul hQ.2 (hB a b ha hab hlog q hq r)
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  calc
    _ = |((∑ n ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun (n : ℕ) => (n : ZMod q) = (r : ZMod q)),
          primeProductMass (auxiliaryPrimes B) z n) - primeNormalizer (auxiliaryPrimes B) z *
            ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊,
              roughResidueWeight (r : ZMod q) (Nat.primesLE (auxiliaryCutoff B)) z n / (n : ℝ)) +
        primeNormalizer (auxiliaryPrimes B) z *
          ((∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊,
              roughResidueWeight (r : ZMod q) (Nat.primesLE (auxiliaryCutoff B)) z n / (n : ℝ)) -
            (∫ t in a..b, roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) z H
              (Real.log t) / t) / q.totient)| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hmass hweighted)

end JointDickman

end OAI
