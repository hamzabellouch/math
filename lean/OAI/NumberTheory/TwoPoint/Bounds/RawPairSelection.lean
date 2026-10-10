import OAI.NumberTheory.TwoPoint.Bounds.PrimeDefectPhase
import OAI.NumberTheory.TwoPoint.Walks.SelectedRawLowerBound

namespace OAI

/-! One selection simultaneously retains raw complex mass and keeps the
coprimality error small. The hypotheses are the actual prime-tail moments. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem select_raw_pair_family {J : ℕ} {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf1 : f 1 = 1) (hg1 : g 1 = 1) (hf : OneBounded f) (hg : OneBounded g)
    (P : Fin J → Finset ℕ) (Q : Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (hQ : ∀ p ∈ Q, p.Prime) (hPQ : Disjoint (primeTuplePool P) Q)
    (W L η γ : ℝ) (hW : 1 ≤ W) (hη : 0 < η) (hγ : 0 ≤ γ)
    (hmass : ∀ j, W ≤ primeHarmonicMass (P j))
    (htotal : paddingTiltNormalizer Q * (∏ j, primeHarmonicMass (P j)) / 2 ≤
      totalPaddingBinMass (primeTupleDivisors P) Q L η)
    (hdD : (∑ p ∈ primeTuplePool P, (1 - ‖f p * g p‖) / (p : ℝ)) ≤ 1 / 100)
    (hdQ : (∑ p ∈ Q, (1 - ‖f p * g p‖) / (p : ℝ)) ≤ 1 / 100)
    (hrD : (∑ p ∈ primeTuplePool P, 1 / (p : ℝ) ^ 2) ≤ γ / 1280)
    (hrQ : (∑ p ∈ Q, 1 / (p : ℝ) ^ 2) ≤ γ / 1280) :
    ∃ A ⊆ eligibleComplexPairs (primeTupleDivisors P) Q (PaddingPairEligible L η),
      totalPaddingBinMass (primeTupleDivisors P) Q L η / 8 ≤ ‖selectedRawCoefficient A f g‖ ∧
      (∑ dq ∈ A, complexPairWeight dq) ≤ totalPaddingBinMass (primeTupleDivisors P) Q L η ∧
      (∑ dq ∈ A, complexPairWeight dq *
        ∑ p ∈ (dq.1 * dq.2).primeFactors, 1 / (p : ℝ)) ≤
          γ * totalPaddingBinMass (primeTupleDivisors P) Q L η / 128 := by
  have hWp : 0 < W := zero_lt_one.trans_le hW
  have hdD0 : 0 ≤ ∑ p ∈ primeTuplePool P, (1 - ‖f p * g p‖) / (p : ℝ) := by
    apply sum_nonneg
    intro p hp
    have hpp := primeTuplePool_prime hprime hp
    apply div_nonneg _ (Nat.cast_nonneg p)
    rw [norm_mul]
    exact sub_nonneg.mpr ((mul_le_mul (hf p hpp.pos) (hg p hpp.pos)
      (norm_nonneg _) zero_le_one).trans (by norm_num))
  have hdsmall : (∑ p ∈ primeTuplePool P, (1 - ‖f p * g p‖) / (p : ℝ)) / W +
      4 * (∑ p ∈ Q, (1 - ‖f p * g p‖) / (p : ℝ)) ≤ 1 / 4 := by
    have hdiv := div_le_self hdD0 hW
    linarith
  obtain ⟨A, hA, hphase⟩ := exists_pair_phase_of_prime_defect hfm hgm hf1 hg1 hf hg
    P Q hprime hdisjoint hQ hPQ W L η hWp hη hmass htotal hdsmall
  refine ⟨A, hA, hphase, selected_pair_mass_le _ _ A L η hη hA, ?_⟩
  have hA' : A ⊆ primeTupleDivisors P ×ˢ retainedPrimeDivisors Q :=
    hA.trans (filter_subset _ _)
  have hb := selected_pair_reciprocal_cost_le P Q hprime hdisjoint hQ hPQ W hWp hmass A hA'
  have hdiv : (∑ p ∈ primeTuplePool P, 1 / (p : ℝ) ^ 2) / W ≤ γ / 1280 :=
    (div_le_self (sum_nonneg (fun _ _ => by positivity)) hW).trans hrD
  have hsmall : (∑ p ∈ primeTuplePool P, 1 / (p : ℝ) ^ 2) / W +
      4 * (∑ p ∈ Q, 1 / (p : ℝ) ^ 2) ≤ γ / 256 := by linarith
  have hV : 0 ≤ paddingTiltNormalizer Q * ∏ j, primeHarmonicMass (P j) :=
    mul_nonneg (paddingTiltNormalizer_pos Q).le
      (prod_nonneg (fun j _ => (hWp.trans_le (hmass j)).le))
  have hs := mul_le_mul_of_nonneg_left hsmall hV
  have ht := mul_le_mul_of_nonneg_left htotal hγ
  exact hb.trans (hs.trans (by nlinarith))

end TwoPointCorrelations

end OAI
