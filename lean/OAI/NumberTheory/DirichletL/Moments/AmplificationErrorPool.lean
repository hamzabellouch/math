import OAI.NumberTheory.DirichletL.Moments.AmplificationSourceError

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationErrorPool
open CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentAmplificationSourceDomain CenteredMomentAmplificationSourcePolynomial
open CenteredMomentAmplificationSourcePool CenteredMomentSourceRow CenteredMomentLiveDomain
open CenteredMomentGaussEnergy CenteredMomentFirstSectors CenteredMomentOriginalChildEnergy
local notation "O" => ActualEisensteinCubic.O

 theorem residual_polynomial_eq_punctured (S : Finset (Ideal O)) (c f : Ideal O → ℂ)
    (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (k : ℕ) (hk : 0<k) (h : O) :
    gaussPolynomial Finset.univ (sourceGenerator (residualColumns S p hp k))
      (sourceGenerator_supported (residualColumns S p hp k))
      (fun I : supportedColumns (residualColumns S p hp k) => c ((Ideal.span {p})^k*I)*f I) h=
    gaussPolynomial Finset.univ
      (sourceGenerator (residualPool ((Ideal.span {p})^k) (pow_ne_zero k hs.1) S))
      (sourceGenerator_supported (residualPool ((Ideal.span {p})^k) (pow_ne_zero k hs.1) S))
      (fun I : supportedColumns (residualPool ((Ideal.span {p})^k) (pow_ne_zero k hs.1) S) =>
        (if IsCoprime ((Ideal.span {p})^k) (I:Ideal O) then c ((Ideal.span {p})^k*I) else 0)*f I) h := by
  let C := (Ideal.span {p})^k
  let Q := residualPool C (pow_ne_zero k hs.1) S
  refine (source_gaussPolynomial _ (fun I => c (C*I)*f I) h).trans ?_
  refine Eq.trans ?_ (source_gaussPolynomial Q
    (fun I => (if IsCoprime C I then c (C*I) else 0)*f I) h).symm
  rw [supported_residualColumns,residualColumns_eq S p hp hs hpp k,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  dsimp only [C]
  rw [IsCoprime.pow_left_iff hk]
  split_ifs <;> simp only [zero_mul]

 theorem residual_energy_eq_punctured (S : Finset (Ideal O)) (c f : Ideal O → ℂ)
    (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (k : ℕ) (hk : 0<k) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceGaussEnergy (residualColumns S p hp k) (fun I => c ((Ideal.span {p})^k*I)) f W K=
      sourceGaussEnergy (residualPool ((Ideal.span {p})^k) (pow_ne_zero k hs.1) S)
        (fun I => if IsCoprime ((Ideal.span {p})^k) I then c ((Ideal.span {p})^k*I) else 0) f W K := by
  unfold sourceGaussEnergy gaussEnergy
  apply tsum_congr
  intro h
  rw [residual_polynomial_eq_punctured S c f p hp hs hpp k hk h]

end SevenEighths.CenteredMomentAmplificationErrorPool

end

end OAI
