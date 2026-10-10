import OAI.NumberTheory.CubicMoment.Angular.AngularSemiprimeSmoothed

namespace OAI

/-! Every original semiprime low-height piece is negligible, with its
product envelope and the full Mellin line retained. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_semiprime_piece_log_saving
    (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0) (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput a)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6)) (k Ct : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop, ∀ H : ℝ, 0 < H → ∀ i j : ℕ,
      ‖semiprimePartitionPiece ℓ H ((1+Real.log X)^Ct) X i j‖ ≤
        K*X^(5/6:ℝ)/(1+Real.log X)^k := by
  obtain ⟨K₀,hK₀,hbound⟩ := angular_semiprime_smoothed_log_saving ℓ hSW hℓ hpub hHuxley hperiod
    hMV hC hGI hGQ hVor hGamma (k+Ct) (Ct+1)
  refine ⟨(8/3)*Real.log 2*K₀,by positivity,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with X hbound hX hlog
  intro H hH i j
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hL : 0 < 1+Real.log X := by linarith
  have hLp : 2 ≤ 1+Real.log X := by linarith
  by_cases hzero : semiprimePartitionPiece ℓ H ((1+Real.log X)^Ct) X i j = 0
  · rw [hzero,norm_zero]
    positivity
  have he : semiprimePartitionPiece ℓ H ((1+Real.log X)^Ct) X i j =
      ∫ t : ℝ, lowHeightWeight H ((1+Real.log X)^Ct) t*
        (Complex.exp ((-Real.log X*t:ℝ)*Complex.I)*angularSemiprimeSmoothedPolynomial ℓ X i j t) := by
    rw [semiprimePartitionPiece_full_support ℓ H _ hXp i j,
      centered_product_low_integral _ _ _ _ ℓ primeProductEnvelope X X _ hH]
    apply integral_congr_ae
    filter_upwards with t
    dsimp only [angularSemiprimeSmoothedPolynomial]
    ring
  rw [he]
  have hh := lowHeightWeight_integral_bound H (pow_pos hL Ct)
    (by positivity : 0 ≤ K₀*X^(5/6:ℝ)/(1+Real.log X)^(k+Ct))
    (fun t => Complex.exp ((-Real.log X*t:ℝ)*Complex.I)*angularSemiprimeSmoothedPolynomial ℓ X i j t)
    (by
      intro t ht
      rw [norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
      apply hbound H ((1+Real.log X)^Ct) i j t hzero
      have habs : |t| ≤ (4/3)*(1+Real.log X)^Ct := abs_le.mpr ⟨by linarith [ht.1],ht.2⟩
      apply habs.trans
      rw [pow_succ]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        ((by norm_num : (4/3:ℝ) ≤ 2).trans hLp) (pow_nonneg hL.le Ct))
  apply hh.trans_eq
  rw [pow_add]
  field_simp [hL.ne']

end CubicFirstMoment

end

end OAI
