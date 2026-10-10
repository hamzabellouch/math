import OAI.NumberTheory.DirichletL.Moments.AmplificationSourceDomain

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationSourcePolynomial
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentAmplificationSource CenteredMomentAmplificationSourceDomain
open CenteredMomentGaussEnergy CenteredMomentSupportedCorrelation
open CenteredMomentSourceRow CenteredMomentLiveDomain
local notation "O" => ActualEisensteinCubic.O

 theorem residual_primaryGaussRow (p : O) (hp : Prime p)
    (hpp : goodLambda^2 ∣ p-1) (I : Ideal O) (hI : Supported I) (h : O) :
    primaryGaussRow (residualIdeal p hp I) h=
      gaussRow (primeRemainder p hp (primaryGenerator I)
        (supported_primaryGenerator_ne_zero I hI))
        (primeRemainder_supported p hp (primaryGenerator I)
          (by rw [primary_span_supported I hI];exact hI)) h := by
  simp only [primaryGaussRow,dite_eq_left (residualIdeal_supported p hp I hI),
    residualIdeal_generator p hp hpp I hI]

 theorem supported_residualColumns (S : Finset (Ideal O)) (p : O) (hp : Prime p) (k : ℕ) :
    supportedColumns (residualColumns S p hp k)=residualColumns S p hp k := by
  apply Finset.filter_eq_self.mpr
  exact residualColumns_supported S p hp k

theorem remainder_polynomial (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (p : O) (hp : Prime p) (hpp : goodLambda^2 ∣ p-1) (k : ℕ) (h : O) :
    gaussPolynomial Finset.univ
      (fun I : supportedColumns S => primeRemainder p hp (sourceGenerator S I)
        (supported_element_ne_zero _ (sourceGenerator_supported S I)))
      (fun I => primeRemainder_supported p hp (sourceGenerator S I) (sourceGenerator_supported S I))
      (fun I => if multiplicity p (sourceGenerator S I)=k then
        c I*residualCharacter p k
          (primeRemainder p hp (sourceGenerator S I)
            (supported_element_ne_zero _ (sourceGenerator_supported S I))) else 0) h =
      gaussPolynomial Finset.univ (sourceGenerator (residualColumns S p hp k))
        (sourceGenerator_supported (residualColumns S p hp k))
        (fun I : supportedColumns (residualColumns S p hp k) =>
          c ((Ideal.span {p})^k*I)*residualCharacter p k (primaryGenerator I)) h := by
  let f : Ideal O → ℂ := fun I => residualCharacter p k (primaryGenerator I)*primaryGaussRow I h
  have he := residual_column_sum S p hp k c f
  have hl : (∑ I∈valuationColumns S p k,c I*f (residualIdeal p hp I))=
      gaussPolynomial Finset.univ
        (fun I : supportedColumns S => primeRemainder p hp (sourceGenerator S I)
          (supported_element_ne_zero _ (sourceGenerator_supported S I)))
        (fun I => primeRemainder_supported p hp (sourceGenerator S I) (sourceGenerator_supported S I))
        (fun I => if multiplicity p (sourceGenerator S I)=k then
          c I*residualCharacter p k
            (primeRemainder p hp (sourceGenerator S I)
              (supported_element_ne_zero _ (sourceGenerator_supported S I))) else 0) h := by
    rw [valuationColumns,Finset.sum_filter]
    unfold gaussPolynomial
    rw [← Finset.sum_coe_sort (supportedColumns S)]
    apply Finset.sum_congr rfl
    intro I hI
    dsimp only [sourceGenerator]
    rw [show f (residualIdeal p hp I)=
      residualCharacter p k (primeRemainder p hp (primaryGenerator I)
        (supported_primaryGenerator_ne_zero I (Finset.mem_filter.mp I.property).2))*
      gaussRow (primeRemainder p hp (primaryGenerator I)
        (supported_primaryGenerator_ne_zero I (Finset.mem_filter.mp I.property).2))
        (primeRemainder_supported p hp (primaryGenerator I)
          (by rw [primary_span_supported I (Finset.mem_filter.mp I.property).2]
              exact (Finset.mem_filter.mp I.property).2)) h by
      dsimp only [f]
      rw [residualIdeal_generator p hp hpp I (Finset.mem_filter.mp I.property).2,
        residual_primaryGaussRow p hp hpp I (Finset.mem_filter.mp I.property).2 h]]
    split_ifs with hk <;> simp only [hk, ite_true, ite_false, zero_mul]
    ring
  refine hl.symm.trans (he.trans ?_)
  have hh := source_gaussPolynomial (residualColumns S p hp k)
    (fun I => c ((Ideal.span {p})^k*I)*residualCharacter p k (primaryGenerator I)) h
  refine Eq.trans ?_ hh.symm
  rw [supported_residualColumns]
  apply Finset.sum_congr rfl
  intro I hI
  dsimp only [f]
  ring

end SevenEighths.CenteredMomentAmplificationSourcePolynomial

end

end OAI
