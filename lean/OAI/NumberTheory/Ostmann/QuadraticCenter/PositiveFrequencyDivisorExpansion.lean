import OAI.NumberTheory.Ostmann.QuadraticCenter.FrequencySplit
import OAI.NumberTheory.Ostmann.QuadraticCenter.PositiveFrequencyDivisor

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def divisorFourierFrequency (q d : ℕ) (A : ∀ p : ℕ, Finset (ZMod p))
    (mInv : ℤ) (a R : ℝ) (u : ℤ) : ℂ :=
  letI : ∀ p : d.primeFactors, NeZero p.val := fun p => ⟨(divisor_coordinate_prime d p).ne_zero⟩
  letI : NeZero (∏ p : d.primeFactors, p.val) := ⟨divisor_coordinates_product_ne_zero d⟩
  quadraticFourierFrequency q (∏ p : d.primeFactors, p.val)
    (centeredProduct (fun p : d.primeFactors => p.val) (divisor_coordinates_coprime d)
      (fun p => A p.val)) (mInv : ZMod (∏ p : d.primeFactors, p.val)) a R u

theorem normalized_divisor_positive_frequency_eq_arrays {L q d : ℕ}
    (hL : Squarefree L) (hq : Squarefree q) (hd : Squarefree d)
    (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℤ) (h θ : ℝ)
    {R : ℝ} (hR : 0 < R) (B : ℕ) (hB : R*d ≤ (B : ℝ)) :
    (Real.sqrt (R*d) : ℂ)⁻¹ *
      (∑' n : ℕ, divisorFourierFrequency q d A mInv (h+θ) R ((n : ℤ)+1)) =
      ∑ P ∈ q.divisors, (-1 : ℂ) ^ P.primeFactors.card *
        ∑ s ∈ (Finset.Icc 1 B).filter (fun s => Squarefree s ∧ s.Coprime L),
          ((jacobiSym (s : ℤ) q : ℂ) / (Real.sqrt (s : ℝ) : ℂ)) *
            ∑ v ∈ L.divisors, ((jacobiSym (v : ℤ) q : ℂ) / (Real.sqrt (v : ℝ) : ℂ)) *
              divisorQuadraticSumP d A mInv s v P R h θ := by
  let : ∀ p : d.primeFactors, NeZero p.val := fun p => ⟨(divisor_coordinate_prime d p).ne_zero⟩
  let : NeZero (∏ p : d.primeFactors, p.val) := ⟨divisor_coordinates_product_ne_zero d⟩
  have ht := normalized_centered_positive_frequency_eq_arrays
    (fun p : d.primeFactors => p.val) (divisor_coordinates_coprime d)
    (fun p => A p.val) (mInv : ZMod (∏ p : d.primeFactors, p.val)) hL hq h θ hR B
    (by simpa only [divisor_coordinates_product hd] using hB)
  change (Real.sqrt (R*(∏ p : d.primeFactors, p.val)) : ℂ)⁻¹ *
    (∑' n : ℕ, divisorFourierFrequency q d A mInv (h+θ) R ((n : ℤ)+1)) = _ at ht
  rw [show Real.sqrt (R*(∏ p : d.primeFactors, p.val)) = Real.sqrt (R*d) by
    rw [divisor_coordinates_product hd]] at ht
  exact ht

theorem divisorFourierFrequency_summable (q d : ℕ)
    (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℤ) (a : ℝ) {R : ℝ} (hR : 0 < R) :
    Summable (divisorFourierFrequency q d A mInv a R) := by
  let : ∀ p : d.primeFactors, NeZero p.val := fun p => ⟨(divisor_coordinate_prime d p).ne_zero⟩
  let : NeZero (∏ p : d.primeFactors, p.val) := ⟨divisor_coordinates_product_ne_zero d⟩
  exact quadraticFourierFrequency_summable q _ _
    (norm_centeredProduct_le_one (fun p : d.primeFactors => p.val)
      (divisor_coordinates_coprime d) (fun p => A p.val)) _ _ hR

theorem divisor_positive_frequency_eq_array {L q : ℕ}
    (hL : Squarefree L) (hq : Squarefree q) (lam : ℝ)
    (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℕ → ℤ) (h θ : ℝ)
    {R : ℝ} (hR : 0 < R) (B : ℕ) (hB : R*L ≤ (B : ℝ)) :
    (∑ d ∈ L.divisors,
      ((lam : ℂ)^d.primeFactors.card * (jacobiSym (d : ℤ) q : ℂ) /
        (Real.sqrt (R*d) : ℂ)) *
        (∑' n : ℕ, divisorFourierFrequency q d A (mInv d) (h+θ) R ((n : ℤ)+1))) =
      ∑ P ∈ q.divisors, (-1 : ℂ)^P.primeFactors.card *
        ∑ s ∈ (Finset.Icc 1 B).filter (fun s => Squarefree s ∧ s.Coprime L),
          (jacobiSym (s : ℤ) q : ℂ) * positiveDivisorArray L q lam A mInv P R h θ s := by
  classical
  let I := (Finset.Icc 1 B).filter (fun s => Squarefree s ∧ s.Coprime L)
  have hBd (d : ℕ) (hd : d ∈ L.divisors) : R*d ≤ (B : ℝ) := by
    have hdL : (d : ℝ) ≤ L := by
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hL.ne_zero)
        (Nat.dvd_of_mem_divisors hd)
    exact (mul_le_mul_of_nonneg_left hdL hR.le).trans hB
  have heach (d : ℕ) (hd : d ∈ L.divisors) :=
    normalized_divisor_positive_frequency_eq_arrays hL hq
      (hL.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)) A (mInv d) h θ hR B (hBd d hd)
  calc
    _ = ∑ d ∈ L.divisors, ∑ P ∈ q.divisors, ∑ s ∈ I, ∑ v ∈ L.divisors,
        (-1 : ℂ)^P.primeFactors.card * (jacobiSym (s : ℤ) q : ℂ) *
          ((Real.sqrt (s : ℝ) : ℂ)⁻¹ *
            ((jacobiSym (v : ℤ) q : ℂ) / (Real.sqrt (v : ℝ) : ℂ))) *
          ((lam : ℂ)^d.primeFactors.card * (jacobiSym (d : ℤ) q : ℂ) *
            divisorQuadraticSumP d A (mInv d) s v P R h θ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [div_eq_mul_inv, mul_assoc, heach d hd]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro P hP
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _ = ∑ P ∈ q.divisors, ∑ d ∈ L.divisors, ∑ s ∈ I, ∑ v ∈ L.divisors,
        (-1 : ℂ)^P.primeFactors.card * (jacobiSym (s : ℤ) q : ℂ) *
          ((Real.sqrt (s : ℝ) : ℂ)⁻¹ *
            ((jacobiSym (v : ℤ) q : ℂ) / (Real.sqrt (v : ℝ) : ℂ))) *
          ((lam : ℂ)^d.primeFactors.card * (jacobiSym (d : ℤ) q : ℂ) *
            divisorQuadraticSumP d A (mInv d) s v P R h θ) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro P hP
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum, positiveDivisorArray]
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro d hd
      ring

end Ostmann.QuadraticCenter

end

end OAI
