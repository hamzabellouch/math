import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeBlockEstimate
import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeFullSupport
import OAI.NumberTheory.CubicMoment.Estimates.CenteredMellinWindow

namespace OAI

/-! The actual semiprime kernel in low height and a finite Mellin window.
All coordinate cutoffs have been reconstructed before cancellation is used. -/
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma semiprimeBlockPolynomial_eq_centered (X : ℝ) (i j : ℕ) (u : ℝ) :
    semiprimeBlockPolynomial X i j u =
      centeredProductPolynomial (semiprimeFullSupport X i) (semiprimeFullSupport X j)
        (semiprimePartitionCoefficient X i) (semiprimePartitionCoefficient X j) 0 u := by
  simp only [semiprimeBlockPolynomial,centeredProductPolynomial,semiprimeFullSupport,
    semiprimePartitionCoefficient,theta_zero,mul_one]

def semiprimeLowMellinWindow (H T X S : ℝ) (i j : ℕ) : ℂ :=
  centeredLowMellinWindow (semiprimeFullSupport X i) (semiprimeFullSupport X j)
    (semiprimePartitionCoefficient X i) (semiprimePartitionCoefficient X j)
    0 primeProductEnvelope X X H T S

theorem semiprimePartitionPiece_mellin {X H : ℝ} (hX : 0 < X) (hH : 0 < H)
    (T : ℝ) (i j : ℕ) :
    semiprimePartitionPiece 0 H T X i j =
      ∫ t : ℝ, (lowHeightWeight H T t*Complex.exp ((-Real.log X*t:ℝ)*Complex.I))*
        ∫ τ : ℝ, zeroLineMellinWeight primeProductEnvelope X τ*
          semiprimeBlockPolynomial X i j (t-τ) := by
  rw [semiprimePartitionPiece_full_support 0 H T hX i j]
  have hb := centered_product_low_mellin (semiprimeFullSupport X i) (semiprimeFullSupport X j)
    (semiprimePartitionCoefficient X i) (semiprimePartitionCoefficient X j)
    (fun p hp => ((semiprimeFullSupport_mem X i p).mp hp).1.1)
    (fun q hq => ((semiprimeFullSupport_mem X j q).mp hq).1.1)
    0 primeProductEnvelope primeProductEnvelope_compact primeProductEnvelope_positive
    primeProductEnvelope_smooth hX X T hH
  simpa only [← semiprimeBlockPolynomial_eq_centered] using hb

lemma semiprime_low_mellin_height {L : ℝ} (hL : 2 ≤ L) (Ct Cs : ℕ)
    {t τ : ℝ} (ht : t ∈ Icc (-(4/3)*L^Ct) ((4/3)*L^Ct))
    (hτ : τ ∈ Icc (-(L^Cs)) (L^Cs)) : |t-τ| ≤ L^(Ct+Cs+2) := by
  have hL1 : 1 ≤ L := by linarith
  have ht' : |t| ≤ (4/3)*L^Ct := abs_le.mpr ⟨by linarith [ht.1],ht.2⟩
  have hτ' : |τ| ≤ L^Cs := abs_le.mpr hτ
  have hCt : L^Ct ≤ L^(Ct+Cs) := pow_le_pow_right₀ hL1 (Nat.le_add_right _ _)
  have hCs : L^Cs ≤ L^(Ct+Cs) := pow_le_pow_right₀ hL1 (Nat.le_add_left _ _)
  calc
    _ ≤ |t|+|τ| := abs_sub t τ
    _ ≤ (4/3)*L^Ct+L^Cs := add_le_add ht' hτ'
    _ ≤ (7/3)*L^(Ct+Cs) := by linarith
    _ ≤ L^(Ct+Cs)*L^2 := by
      have hsq : (7/3:ℝ) ≤ L^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hsq (pow_nonneg (by linarith : 0 ≤ L) (Ct+Cs))]
    _ = _ := (pow_add _ _ _).symm

theorem semiprime_low_mellin_window_log_saving
    (hSW : KummerPrimeSiegelWalfisz) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput a)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (k Ct Cs : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop, ∀ (H : ℝ) (i j : ℕ),
      semiprimePartitionPiece 0 H ((1+Real.log X)^Ct) X i j ≠ 0 →
      ‖semiprimeLowMellinWindow H ((1+Real.log X)^Ct) X ((1+Real.log X)^Cs) i j‖ ≤
        K*X^(5/6:ℝ)/(1+Real.log X)^k := by
  obtain ⟨K₀,hK₀,hbound⟩ := semiprime_block_log_saving hSW hpub hHuxley hperiod hMV hC
    hGI hGQ hVor hGamma (k+Ct) (Ct+Cs+2)
  let M := zeroLineMellinMass primeProductEnvelope
  have hM : 0 ≤ M := by
    rw [show M = ∫ t : ℝ, ‖zeroLineMellinWeight primeProductEnvelope 1 t‖ from
      (zeroLineMellinWeight_mass primeProductEnvelope (by norm_num)).symm]
    exact integral_nonneg (fun _ => _root_.norm_nonneg _)
  refine ⟨(8/3)*Real.log 2*(M+1)*K₀,by positivity,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with X hb hX hlog
  intro H i j hne
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hL : 0 < 1+Real.log X := by linarith
  have hpoly (t : ℝ) (ht : t ∈ Icc (-(4/3)*(1+Real.log X)^Ct) ((4/3)*(1+Real.log X)^Ct))
      (τ : ℝ) (hτ : τ ∈ Icc (-((1+Real.log X)^Cs)) ((1+Real.log X)^Cs)) :
      ‖centeredProductPolynomial (semiprimeFullSupport X i) (semiprimeFullSupport X j)
        (semiprimePartitionCoefficient X i) (semiprimePartitionCoefficient X j) 0 (t-τ)‖ ≤
        K₀*X^(5/6:ℝ)/(1+Real.log X)^(k+Ct) := by
    rw [← semiprimeBlockPolynomial_eq_centered]
    exact hb H ((1+Real.log X)^Ct) i j (t-τ) hne
      (semiprime_low_mellin_height (by linarith) Ct Cs ht hτ)
  have hh := centeredLowMellinWindow_bound (semiprimeFullSupport X i) (semiprimeFullSupport X j)
    (semiprimePartitionCoefficient X i) (semiprimePartitionCoefficient X j) 0 primeProductEnvelope
    primeProductEnvelope_compact primeProductEnvelope_positive primeProductEnvelope_smooth
    hXp (pow_pos hL Ct) (by positivity : 0 ≤ K₀*X^(5/6:ℝ)/(1+Real.log X)^(k+Ct))
    X H ((1+Real.log X)^Cs) hpoly
  change ‖semiprimeLowMellinWindow H ((1+Real.log X)^Ct) X ((1+Real.log X)^Cs) i j‖ ≤ _ at hh
  calc
    _ ≤ (8/3)*Real.log 2*(1+Real.log X)^Ct*(M*(K₀*X^(5/6:ℝ)/(1+Real.log X)^(k+Ct))) := hh
    _ = ((8/3)*Real.log 2*M*K₀)*X^(5/6:ℝ)/(1+Real.log X)^k := by
      rw [pow_add]
      field_simp [hL.ne']
    _ ≤ _ := by gcongr; linarith

end CubicFirstMoment

end

end OAI
