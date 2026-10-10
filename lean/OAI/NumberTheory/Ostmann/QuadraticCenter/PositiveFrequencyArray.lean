import OAI.NumberTheory.Ostmann.QuadraticCenter.PositiveFrequencySquare

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem normalized_positive_frequency_eq_arrays {L q d : ℕ} [NeZero d]
    (hL : Squarefree L) (hq : Squarefree q) (G : ZMod d → ℂ)
    (mInv : ZMod d) (a : ℝ) {R : ℝ} (hR : 0 < R) (B : ℕ) (hB : R*d ≤ (B : ℝ)) :
    (Real.sqrt (R*d) : ℂ)⁻¹ *
      (∑' n : ℕ, quadraticFourierFrequency q d G mInv a R ((n : ℤ)+1)) =
      ∑ P ∈ q.divisors, (-1 : ℂ) ^ P.primeFactors.card *
        ∑ s ∈ (Finset.Icc 1 B).filter (fun s => Squarefree s ∧ s.Coprime L),
          ((jacobiSym (s : ℤ) q : ℂ) / (Real.sqrt (s : ℝ) : ℂ)) *
            ∑ v ∈ L.divisors, ((jacobiSym (v : ℤ) q : ℂ) / (Real.sqrt (v : ℝ) : ℂ)) *
              positiveFrequencyQuadraticSum d G mInv s v P a R := by
  classical
  rw [quadraticFourierFrequency_positive_finite q d G mInv a hR B hB,
    sum_positive_frequency_jacobi_moebius hL hq B]
  let I := (Finset.Icc 1 B).filter (fun s => Squarefree s ∧ s.Coprime L)
  change (Real.sqrt (R*d) : ℂ)⁻¹ *
    (∑ s ∈ I, ∑ v ∈ L.divisors,
      (jacobiSym (s : ℤ) q : ℂ) * (jacobiSym (v : ℤ) q : ℂ) *
        ∑ P ∈ q.divisors, (-1 : ℂ) ^ P.primeFactors.card *
          ∑ w ∈ (Finset.Icc 1 B).filter (fun w => s*v*w^2 ≤ B ∧ P ∣ w),
            positiveFrequencyAmplitude d G mInv a R (s*v*w^2)) = _
  calc
    _ = ∑ s ∈ I, ∑ v ∈ L.divisors, ∑ P ∈ q.divisors,
        (-1 : ℂ) ^ P.primeFactors.card *
          ((jacobiSym (s : ℤ) q : ℂ) / (Real.sqrt (s : ℝ) : ℂ)) *
          (((jacobiSym (v : ℤ) q : ℂ) / (Real.sqrt (v : ℝ) : ℂ)) *
            positiveFrequencyQuadraticSum d G mInv s v P a R) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      rw [← mul_assoc, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro P hP
      have hs0 : 0 < s := (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1
      have hv0 : 0 < v := Nat.pos_of_mem_divisors hv
      have hinner := positiveFrequencyAmplitude_square_sum_eq G mInv a hR hs0 hv0 P B hB
      calc
        _ = (-1 : ℂ) ^ P.primeFactors.card * (jacobiSym (s : ℤ) q : ℂ) *
            (jacobiSym (v : ℤ) q : ℂ) *
            ((Real.sqrt (R*d) : ℂ)⁻¹ *
              ∑ w ∈ (Finset.Icc 1 B).filter (fun w => s*v*w^2 ≤ B ∧ P ∣ w),
                positiveFrequencyAmplitude d G mInv a R (s*v*w^2)) := by ring
        _ = _ := by rw [hinner]; ring
    _ = ∑ s ∈ I, ∑ P ∈ q.divisors, ∑ v ∈ L.divisors,
        (-1 : ℂ) ^ P.primeFactors.card *
          ((jacobiSym (s : ℤ) q : ℂ) / (Real.sqrt (s : ℝ) : ℂ)) *
          (((jacobiSym (v : ℤ) q : ℂ) / (Real.sqrt (v : ℝ) : ℂ)) *
            positiveFrequencyQuadraticSum d G mInv s v P a R) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact Finset.sum_comm
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro P hP
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro v hv
      ring

theorem normalized_centered_positive_frequency_eq_arrays {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (A : ∀ i, Finset (ZMod (p i))) (mInv : ZMod (∏ i, p i))
    {L q : ℕ} (hL : Squarefree L) (hq : Squarefree q) (h θ : ℝ)
    {R : ℝ} (hR : 0 < R) (B : ℕ) (hB : R*(∏ i, p i : ℕ) ≤ (B : ℝ)) :
    (Real.sqrt (R*(∏ i, p i : ℕ)) : ℂ)⁻¹ *
      (∑' n : ℕ, quadraticFourierFrequency q (∏ i, p i) (centeredProduct p hcop A)
        mInv (h+θ) R ((n : ℤ)+1)) =
      ∑ P ∈ q.divisors, (-1 : ℂ) ^ P.primeFactors.card *
        ∑ s ∈ (Finset.Icc 1 B).filter (fun s => Squarefree s ∧ s.Coprime L),
          ((jacobiSym (s : ℤ) q : ℂ) / (Real.sqrt (s : ℝ) : ℂ)) *
            ∑ v ∈ L.divisors, ((jacobiSym (v : ℤ) q : ℂ) / (Real.sqrt (v : ℝ) : ℂ)) *
              centeredQuadraticSum p hcop A mInv s v P R h θ := by
  simpa only [positiveFrequencyQuadraticSum_centered] using
    normalized_positive_frequency_eq_arrays hL hq (centeredProduct p hcop A) mInv (h+θ) hR B hB

end Ostmann.QuadraticCenter

end

end OAI
