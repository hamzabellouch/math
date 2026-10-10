import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeBlockEstimate
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralSemiprimePrimeEstimate

namespace OAI

/-! Every nonzero semiprime piece has a logarithmically small centered
prime polynomial throughout the required fixed logarithmic height range.
The two coordinate orders are treated by their exact symmetry. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
namespace CubicFirstMoment


theorem semiprime_block_log_saving_actual
    (hSW : KummerPrimeSiegelWalfisz) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (k U : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop, ∀ (H T : ℝ) (i j : ℕ) (u : ℝ),
      semiprimePartitionPiece 0 H T X i j ≠ 0 → |u| ≤ (1+Real.log X)^U →
      ‖semiprimeBlockPolynomial X i j u‖ ≤ K*X^(5/6:ℝ)/(1+Real.log X)^k := by
  obtain ⟨η,G,K₀,B₀,hη,_,hK₀,hbound⟩ := semiprime_prime_bilinear_actual
    hSW hpub hHuxley hperiod hMV hC hGI hGQ  hGamma k (U+1)
  refine ⟨K₀*3^(5/6:ℝ)/(39/100:ℝ)^k,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_semiprime_admissible hη G B₀,
    eventually_semiprime_height_comparison U,
    eventually_const_mul_rpow_le (by norm_num : (39/100:ℝ) < 2/5) 2]
    with X hX hadm hheight hlower
  intro H T i j u hne hu
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hordered (i j : ℕ) (hji : semiprimePartitionScale j ≤ semiprimePartitionScale i)
      (hne : semiprimePartitionPiece 0 H T X i j ≠ 0) :
      ‖semiprimeBlockPolynomial X i j u‖ ≤
        (K₀*3^(5/6:ℝ)/(39/100:ℝ)^k)*X^(5/6:ℝ)/(1+Real.log X)^k := by
    let A := semiprimePartitionScale i
    let B := semiprimePartitionScale j
    have hAp : 0 < A := semiprimePartitionScale_pos i
    have hBp : 0 < B := semiprimePartitionScale_pos j
    obtain ⟨hB₀,hrough,hAlo,hAhi⟩ := hadm 0 H T i j hji hne
    obtain ⟨_,hAB,_,hBL⟩ := semiprimePartitionPiece_nonzero_lengths 0 H T hXp hne
    have hBX : X^(39/100:ℝ) ≤ B := by dsimp [B]; linarith
    have hB1 : 1 ≤ B := (Real.one_le_rpow hX (by norm_num : (0:ℝ) ≤ 39/100)).trans hBX
    have hb := hbound (A/(X^(2/5:ℝ))) (B/(X^(2/5:ℝ))) A B u
      (by positivity) (by positivity) hB1 hB₀ hrough hAlo hAhi
      (hu.trans (hheight B hBX))
    change ‖semiprimeBlockPolynomial X i j u‖ ≤ _ at hb
    exact hb.trans (semiprime_bilinear_scale hX hAp.le hBX hK₀.le hAB k)
  by_cases hji : semiprimePartitionScale j ≤ semiprimePartitionScale i
  · exact hordered i j hji hne
  · rw [semiprimeBlockPolynomial_symm X i j u]
    apply hordered j i (le_of_not_ge hji)
    rwa [semiprimePartitionPiece_symm 0 H T X j i]

end CubicFirstMoment

end

end OAI
