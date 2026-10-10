import OAI.NumberTheory.TwoPoint.Bounds.ComplexPairSelection

namespace OAI

/-! Small prime-defect moments produce a numerical phase-selected family
whose coefficient is comparable to the full retained bin mass. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma exists_pair_phase_of_prime_defect {J : ℕ} {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf1 : f 1 = 1) (hg1 : g 1 = 1) (hf : OneBounded f) (hg : OneBounded g)
    (P : Fin J → Finset ℕ) (Q : Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (hQ : ∀ p ∈ Q, p.Prime) (hPQ : Disjoint (primeTuplePool P) Q)
    (W L η : ℝ) (hW : 0 < W) (hη : 0 < η)
    (hmass : ∀ j, W ≤ primeHarmonicMass (P j))
    (htotal : paddingTiltNormalizer Q * (∏ j, primeHarmonicMass (P j)) / 2 ≤
      totalPaddingBinMass (primeTupleDivisors P) Q L η)
    (hdefect : (∑ p ∈ primeTuplePool P, (1 - ‖f p * g p‖) / (p : ℝ)) / W +
      4 * (∑ p ∈ Q, (1 - ‖f p * g p‖) / (p : ℝ)) ≤ 1 / 4) :
    ∃ A ⊆ eligibleComplexPairs (primeTupleDivisors P) Q (PaddingPairEligible L η),
      totalPaddingBinMass (primeTupleDivisors P) Q L η / 8 ≤
        ‖∑ dq ∈ A, (complexPairWeight dq : ℂ) *
          (f (dq.1 * dq.2) * g (dq.1 * dq.2))‖ := by
  apply exists_eligible_pair_phase (primeTupleDivisors P) Q L η hη
  have hv : 0 ≤ paddingTiltNormalizer Q * ∏ j, primeHarmonicMass (P j) :=
    mul_nonneg (paddingTiltNormalizer_pos Q).le
      (prod_nonneg (fun j _ => (hW.trans_le (hmass j)).le))
  have hD : ∀ d ∈ primeTupleDivisors P, 0 < d := by
    intro d hd
    exact Nat.pos_of_ne_zero (primeTupleDivisors_arithmetic P hprime hdisjoint hd).1.ne_zero
  apply (eligibleComplexPairs_defect_le hf hg (primeTupleDivisors P) Q hD hQ _).trans
  have hb := tuple_padding_modulus_defect hfm hgm hf1 hg1 hf hg P Q hprime hdisjoint
    hQ hPQ W hW hmass
  have hc := padding_modulus_defect_cost_le hf hg Q hQ
  have hs := mul_le_mul_of_nonneg_left
    (add_le_add (le_refl ((∑ p ∈ primeTuplePool P, (1 - ‖f p * g p‖) / (p : ℝ)) / W)) hc) hv
  have ht := mul_le_mul_of_nonneg_left hdefect hv
  exact hb.trans (hs.trans (ht.trans (by linarith)))

end TwoPointCorrelations

end OAI
