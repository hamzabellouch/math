import OAI.NumberTheory.TwoPoint.Bounds.ComplexRawSelection
import OAI.NumberTheory.TwoPoint.Bounds.PairModulusDefect

namespace OAI

/-! Phase selection on the literal finite numerical pair family. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def eligibleComplexPairs (D Q : Finset ℕ)
    (eligible : ℕ → ℕ → Prop) : Finset (ℕ × ℕ) :=
  (D ×ˢ retainedPrimeDivisors Q).filter (fun dq => eligible dq.1 dq.2)

noncomputable def complexPairWeight (dq : ℕ × ℕ) : ℝ :=
  (4 : ℝ) ^ dq.2.primeFactors.card / (dq.1 * dq.2 : ℕ)

lemma complexPairWeight_nonneg (dq : ℕ × ℕ) : 0 ≤ complexPairWeight dq := by
  unfold complexPairWeight
  positivity

lemma eligibleComplexPairs_sum {M : Type*} [AddCommMonoid M]
    (D Q : Finset ℕ) (eligible : ℕ → ℕ → Prop) (F : ℕ × ℕ → M) :
    (∑ dq ∈ eligibleComplexPairs D Q eligible, F dq) =
      ∑ d ∈ D, ∑ q ∈ retainedPrimeDivisors Q, if eligible d q then F (d, q) else 0 := by
  rw [eligibleComplexPairs, sum_filter, sum_product]

lemma eligibleComplexPairs_mass (D Q : Finset ℕ) (L η : ℝ) (hη : 0 < η) :
    (∑ dq ∈ eligibleComplexPairs D Q (PaddingPairEligible L η), complexPairWeight dq) =
      totalPaddingBinMass D Q L η := by
  rw [eligibleComplexPairs_sum, totalPaddingBinMass_eq D Q L η hη]
  rfl

lemma eligibleComplexPairs_defect_le {f g : ℕ → ℂ}
    (hf : OneBounded f) (hg : OneBounded g)
    (D Q : Finset ℕ) (hD : ∀ d ∈ D, 0 < d) (hQ : ∀ p ∈ Q, p.Prime)
    (eligible : ℕ → ℕ → Prop) :
    (∑ dq ∈ eligibleComplexPairs D Q eligible, complexPairWeight dq *
      (1 - ‖f (dq.1 * dq.2) * g (dq.1 * dq.2)‖)) ≤
      ∑ d ∈ D, ∑ q ∈ retainedPrimeDivisors Q,
        (4 : ℝ) ^ q.primeFactors.card / (d * q : ℕ) * (1 - ‖f (d * q) * g (d * q)‖) := by
  rw [eligibleComplexPairs_sum]
  apply sum_le_sum
  intro d hd
  apply sum_le_sum
  intro q hq
  by_cases he : eligible d q
  · simp only [he, ite_true, complexPairWeight, le_refl]
  · simp only [he, ite_false]
    apply mul_nonneg (by positivity)
    have hu := Nat.mul_pos (hD d hd) (retainedPrimeDivisor_pos Q hQ hq)
    rw [norm_mul]
    exact sub_nonneg.mpr ((mul_le_mul (hf _ hu) (hg _ hu)
      (norm_nonneg _) zero_le_one).trans (by norm_num))

lemma exists_eligible_pair_phase {f g : ℕ → ℂ} (D Q : Finset ℕ)
    (L η : ℝ) (hη : 0 < η)
    (hdefect : (∑ dq ∈ eligibleComplexPairs D Q (PaddingPairEligible L η),
      complexPairWeight dq * (1 - ‖f (dq.1 * dq.2) * g (dq.1 * dq.2)‖)) ≤
        totalPaddingBinMass D Q L η / 2) :
    ∃ A ⊆ eligibleComplexPairs D Q (PaddingPairEligible L η),
      totalPaddingBinMass D Q L η / 8 ≤
        ‖∑ dq ∈ A, (complexPairWeight dq : ℂ) *
          (f (dq.1 * dq.2) * g (dq.1 * dq.2))‖ := by
  have hm := eligibleComplexPairs_mass D Q L η hη
  obtain ⟨A, hA, hbound⟩ := exists_weighted_phase_subset
    (eligibleComplexPairs D Q (PaddingPairEligible L η)) complexPairWeight
    (fun dq => f (dq.1 * dq.2) * g (dq.1 * dq.2))
    (fun dq _ => complexPairWeight_nonneg dq) (by rwa [hm])
  exact ⟨A, hA, by rwa [hm] at hbound⟩

end TwoPointCorrelations

end OAI
