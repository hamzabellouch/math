import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeHeightEstimate
import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeRange

namespace OAI

/-! The genuine semiprime Gauss polynomial has a uniform dyadic height
mean throughout the range used to truncate its Mellin transform. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def semiprimeGaussPolynomial (X : ℝ) (i j : ℕ) (u : ℝ) : ℂ :=
  let A := semiprimePartitionScale i
  let B := semiprimePartitionScale j
  ∑ p ∈ fullPrimeSupport 2 (fun _ : Unit => semiprimeSmoothWeight (A/X^(2/5:ℝ))) (fun _ => A) (),
    ∑ q ∈ fullPrimeSupport 2 (fun _ : Unit => semiprimeSmoothWeight (B/X^(2/5:ℝ))) (fun _ => B) (),
      semiprimeSmoothWeight (A/X^(2/5:ℝ)) (norm p/A)*
        semiprimeSmoothWeight (B/X^(2/5:ℝ)) (norm q/B)*gauss (p*q)*normTwist u (p*q)

lemma semiprimeGaussPolynomial_symm (X : ℝ) (i j : ℕ) (u : ℝ) :
    semiprimeGaussPolynomial X i j u = semiprimeGaussPolynomial X j i u := by
  unfold semiprimeGaussPolynomial
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [mul_comm q p]
  ring

lemma semiprime_height_power {X B : ℝ} (hX : 1 ≤ X) (hB : X^(39/100:ℝ) ≤ B) :
    X^(13/100:ℝ) ≤ B^(7/20:ℝ) := by
  calc
    _ ≤ X^((39/100:ℝ)*(7/20)) :=
      Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
    _ = (X^(39/100:ℝ))^(7/20:ℝ) := Real.rpow_mul (zero_le_one.trans hX) _ _
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg (zero_le_one.trans hX) _) hB (by norm_num)

theorem semiprime_gauss_height_log_saving
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) (k : ℕ) :
    ∃ (K : ℝ) (m : ℕ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (H T₀ u T : ℝ) (i j : ℕ), semiprimePartitionPiece 0 H T₀ X i j ≠ 0 →
      (1+Real.log X)^m ≤ T → T ≤ X^(13/100:ℝ) → |u| ≤ X^(13/100:ℝ) →
      dyadicHeightMean (fun t => ‖semiprimeGaussPolynomial X i j (u+t)‖) T ≤
        K*X^(5/6:ℝ)/(1+Real.log X)^k := by
  obtain ⟨η,G,K₀,B₀,m,hη,_,hK₀,hbound⟩ := semiprime_prime_height_bilinear
    hpub hHuxley hperiod hMV hC hGI hGQ k
  refine ⟨K₀*3^(5/6:ℝ)/(39/100:ℝ)^k,m,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (3:ℝ),eventually_semiprime_admissible hη G B₀,
    eventually_const_mul_rpow_le (by norm_num : (39/100:ℝ) < 2/5) 2]
    with X hX hadm hlower
  intro H T₀ u T i j hne hT hThi hu
  have hX1 : 1 ≤ X := by linarith
  have hXp : 0 < X := by linarith
  have hordered (i j : ℕ) (hji : semiprimePartitionScale j ≤ semiprimePartitionScale i)
      (hne : semiprimePartitionPiece 0 H T₀ X i j ≠ 0) :
      dyadicHeightMean (fun t => ‖semiprimeGaussPolynomial X i j (u+t)‖) T ≤
        (K₀*3^(5/6:ℝ)/(39/100:ℝ)^k)*X^(5/6:ℝ)/(1+Real.log X)^k := by
    let A := semiprimePartitionScale i
    let B := semiprimePartitionScale j
    have hAp : 0 < A := semiprimePartitionScale_pos i
    have hBp : 0 < B := semiprimePartitionScale_pos j
    obtain ⟨hB₀,hrough,hAlo,hAhi⟩ := hadm 0 H T₀ i j hji hne
    obtain ⟨_,hAB,_,hBL⟩ := semiprimePartitionPiece_nonzero_lengths 0 H T₀ hXp hne
    have hBX : X^(39/100:ℝ) ≤ B := by dsimp [B]; linarith
    have hB1 : 1 ≤ B := (Real.one_le_rpow hX1 (by norm_num : (0:ℝ) ≤ 39/100)).trans hBX
    have hBXhi : B ≤ X := by
      have hBB : B*B ≤ 3*X := (mul_le_mul_of_nonneg_right hji hBp.le).trans hAB
      nlinarith
    have hlog : 1+Real.log B ≤ 1+Real.log X := by linarith [Real.log_le_log hBp hBXhi]
    have hb := hbound (A/X^(2/5:ℝ)) (B/X^(2/5:ℝ)) A B u T
      (by positivity) (by positivity) hB1 hB₀ hrough
      ((Real.rpow_le_rpow_of_exponent_le hB1 (by linarith : 1-η/4 ≤ 1-η/16)).trans hAlo)
      hAhi
      ((pow_le_pow_left₀ (by linarith [Real.log_nonneg hB1]) hlog m).trans hT)
      (hThi.trans (semiprime_height_power hX1 hBX))
      (hu.trans (semiprime_height_power hX1 hBX))
    change dyadicHeightMean (fun t => ‖semiprimeGaussPolynomial X i j (u+t)‖) T ≤ _ at hb
    exact hb.trans (semiprime_bilinear_scale hX1 hAp.le hBX hK₀.le hAB k)
  by_cases hji : semiprimePartitionScale j ≤ semiprimePartitionScale i
  · exact hordered i j hji hne
  · have hh := hordered j i (le_of_not_ge hji)
      (by rwa [semiprimePartitionPiece_symm 0 H T₀ X j i])
    simpa only [semiprimeGaussPolynomial_symm X j i] using hh

end CubicFirstMoment

end

end OAI
