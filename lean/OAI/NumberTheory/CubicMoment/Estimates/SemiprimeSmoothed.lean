import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeMellinComplement

namespace OAI

/-! Full Mellin transfer for the actual semiprime pieces. Every Mellin
frequency is included before the low-height kernel is estimated. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def semiprimeSmoothedPolynomial (X : ℝ) (i j : ℕ) (u : ℝ) : ℂ :=
  centeredProductSmoothed (semiprimeFullSupport X i) (semiprimeFullSupport X j)
    (semiprimePartitionCoefficient X i) (semiprimePartitionCoefficient X j)
    0 primeProductEnvelope X u

theorem semiprime_smoothed_log_saving
    (hSW : KummerPrimeSiegelWalfisz) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput a)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6)) (k U : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop, ∀ (H T u : ℝ) (i j : ℕ),
      semiprimePartitionPiece 0 H T X i j ≠ 0 → |u| ≤ (1+Real.log X)^U →
      ‖semiprimeSmoothedPolynomial X i j u‖ ≤ K*X^(5/6:ℝ)/(1+Real.log X)^k := by
  obtain ⟨Kc,m,hKc,hcomp⟩ := semiprime_mellin_complement hpub hHuxley hperiod hMV hC hGI hGQ
  obtain ⟨K₀,hK₀,hblock⟩ := semiprime_block_log_saving hSW hpub hHuxley hperiod hMV hC
    hGI hGQ hVor hGamma k (U+(m+k)+2)
  let M := zeroLineMellinMass primeProductEnvelope
  have hM : 0 ≤ M := by
    rw [show M = ∫ t : ℝ, ‖zeroLineMellinWeight primeProductEnvelope 1 t‖ from
      (zeroLineMellinWeight_mass primeProductEnvelope (by norm_num)).symm]
    exact integral_nonneg (fun _ => _root_.norm_nonneg _)
  refine ⟨M*K₀+Kc,by positivity,?_⟩
  filter_upwards [hcomp,hblock,eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    overlap_power_log_saving (by norm_num : (0:ℝ) < 13/100) U 0]
    with X hcomp hblock hX hlog hpower
  intro H T u i j hne hu
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hL : 0 < 1+Real.log X := by linarith
  have hL1 : 1 ≤ 1+Real.log X := by linarith
  let S := (1+Real.log X)^(m+k)
  have hS : (1+Real.log X)^m ≤ S := pow_le_pow_right₀ hL1 (Nat.le_add_right _ _)
  have huX : |u| ≤ X^(13/100:ℝ) := by
    apply hu.trans
    apply (div_le_one (Real.rpow_pos_of_pos hXp _)).mp
    simpa only [Nat.mul_zero,pow_zero,div_one] using hpower
  have htail := hcomp H T u S i j hne hS huX
  have hlocal : ‖centeredMellinWindow (semiprimeFullSupport X i) (semiprimeFullSupport X j)
      (semiprimePartitionCoefficient X i) (semiprimePartitionCoefficient X j)
      0 primeProductEnvelope X S u‖ ≤ M*(K₀*X^(5/6:ℝ)/(1+Real.log X)^k) := by
    apply centeredMellinWindow_bound _ _ _ _ _ _ primeProductEnvelope_compact
      primeProductEnvelope_positive primeProductEnvelope_smooth hXp (by positivity)
    intro τ hτ
    simp_rw [←semiprimeBlockPolynomial_eq_centered X i j]
    apply hblock H T i j (u-τ) hne
    apply semiprime_low_mellin_height (by linarith : 2 ≤ 1+Real.log X) U (m+k) _ hτ
    exact ⟨by linarith [neg_abs_le u,pow_nonneg hL.le U],
      by linarith [le_abs_self u,pow_nonneg hL.le U]⟩
  have he := centered_product_mellin_complement (semiprimeFullSupport X i)
    (semiprimeFullSupport X j) (semiprimePartitionCoefficient X i)
    (semiprimePartitionCoefficient X j)
    (fun p hp => (semiprimeFullSupport_bounds hXp i hp).1)
    (fun p hp => (semiprimeFullSupport_bounds hXp j hp).1)
    0 primeProductEnvelope primeProductEnvelope_compact primeProductEnvelope_positive
    primeProductEnvelope_smooth hXp S u
  change semiprimeSmoothedPolynomial X i j u = _ at he
  simp_rw [←semiprimeBlockPolynomial_eq_centered X i j] at he
  have ht : Kc*X^(5/6:ℝ)/S ≤ Kc*X^(5/6:ℝ)/(1+Real.log X)^k :=
    div_le_div_of_nonneg_left (by positivity) (pow_pos hL k)
      (pow_le_pow_right₀ hL1 (Nat.le_add_left k m))
  rw [he]
  apply (norm_add_le _ _).trans
  exact (add_le_add hlocal (htail.trans ht)).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
