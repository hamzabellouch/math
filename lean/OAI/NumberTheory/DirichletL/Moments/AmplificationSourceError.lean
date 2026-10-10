import OAI.NumberTheory.DirichletL.Moments.AmplificationSourcePolynomial
import OAI.NumberTheory.DirichletL.Moments.AmplificationSourcePool
import OAI.NumberTheory.DirichletL.Moments.AmplificationRectangle
import OAI.NumberTheory.DirichletL.Moments.GaussNormalization

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationSourceError
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentAmplificationSource CenteredMomentAmplificationSourceDomain
open CenteredMomentAmplificationSourcePolynomial CenteredMomentAmplificationSourcePool
open CenteredMomentAmplificationRectangle CenteredMomentGaussNormalization
open CenteredMomentGaussEnergy CenteredMomentSupportedCorrelation CenteredMomentSourceRow
local notation "O" => ActualEisensteinCubic.O

 theorem source_error_residual (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (n : ℕ) (h : O) :
    amplificationError Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I : supportedColumns S => c I)
      (fun I => multiplicity p (sourceGenerator S I)) p (n+1) h =
      (primeRoot p (n+1)*errorScalar p hp.ne_zero n h)*
        gaussPolynomial Finset.univ (sourceGenerator (residualColumns S p hp (n+1)))
          (sourceGenerator_supported (residualColumns S p hp (n+1)))
          (fun I : supportedColumns (residualColumns S p hp (n+1)) =>
            c ((Ideal.span {p})^(n+1)*I)*residualCharacter p (n+1) (primaryGenerator I)) h := by
  rw [source_error_shortening S c p hp hs hpp n h,
    remainder_polynomial S c p hp hpp (n+1) h]

theorem normalized_source_error (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (n : ℕ) (h : O) (T : ℝ) (hT : 0<T) :
    amplificationError Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I : supportedColumns S => (Real.sqrt T:ℂ)⁻¹*c I)
      (fun I => multiplicity p (sourceGenerator S I)) p (n+1) h =
      errorScalar p hp.ne_zero n h *
        gaussPolynomial Finset.univ (sourceGenerator (residualColumns S p hp (n+1)))
          (sourceGenerator_supported (residualColumns S p hp (n+1)))
          (fun I : supportedColumns (residualColumns S p hp (n+1)) =>
            (Real.sqrt (T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1)):ℂ)⁻¹*
            (c ((Ideal.span {p})^(n+1)*I)*residualCharacter p (n+1) (primaryGenerator I))) h := by
  rw [source_error_residual S (fun I => (Real.sqrt T:ℂ)⁻¹*c I) p hp hs hpp n h]
  simp only [mul_assoc,gaussPolynomial_const_mul]
  rw [centralRoot_extract p hp.ne_zero (n+1) T hT]
  have hr := primeRoot_ne_zero p hp.ne_zero (n+1)
  field_simp

theorem normalized_source_error_sq (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (n : ℕ) (h : O) (T : ℝ) (hT : 0<T) :
    ‖amplificationError Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I : supportedColumns S => (Real.sqrt T:ℂ)⁻¹*c I)
      (fun I => multiplicity p (sourceGenerator S I)) p (n+1) h‖^2 =
      ‖errorScalar p hp.ne_zero n h‖^2 *
        ‖gaussPolynomial Finset.univ (sourceGenerator (residualColumns S p hp (n+1)))
          (sourceGenerator_supported (residualColumns S p hp (n+1)))
          (fun I : supportedColumns (residualColumns S p hp (n+1)) =>
            (Real.sqrt (T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1)):ℂ)⁻¹*
            (c ((Ideal.span {p})^(n+1)*I)*residualCharacter p (n+1) (primaryGenerator I))) h‖^2 := by
  rw [normalized_source_error S c p hp hs hpp n h T hT,norm_mul,mul_pow]

end SevenEighths.CenteredMomentAmplificationSourceError

end

end OAI
