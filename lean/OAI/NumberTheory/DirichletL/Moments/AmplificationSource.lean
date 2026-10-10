import OAI.NumberTheory.DirichletL.Moments.AmplificationAllocation
import OAI.NumberTheory.DirichletL.Moments.LiveDomain

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationSource
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentAmplificationAllocation CenteredMomentGaussEnergy
open CenteredMomentSupportedCorrelation CenteredMomentSourceRow CenteredMomentLiveDomain
local notation "O" => ActualEisensteinCubic.O

 theorem primeRoot_ne_zero (p : O) (hp : p ≠ 0) (k : ℕ) : primeRoot p k ≠ 0 := by
  unfold primeRoot
  apply Complex.ofReal_ne_zero.mpr
  apply Real.sqrt_ne_zero'.mpr
  apply pow_pos
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hp))

theorem original_error_shortening {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (hap : ∀ i, goodLambda^2 ∣ a i-1) (c : α → ℂ)
    (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (n : ℕ) (h : O) :
    amplificationError S a ha c (fun i => multiplicity p (a i)) p (n+1) h =
      (primeRoot p (n+1)*errorScalar p hp.ne_zero n h)*
        gaussPolynomial S
          (fun i => primeRemainder p hp (a i) (supported_element_ne_zero _ (ha i)))
          (fun i => primeRemainder_supported p hp (a i) (ha i))
          (fun i => if multiplicity p (a i)=n+1 then
            c i*residualCharacter p (n+1)
              (primeRemainder p hp (a i) (supported_element_ne_zero _ (ha i))) else 0) h := by
  unfold amplificationError gaussPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  by_cases hv : multiplicity p (a i)=n+1
  · simp only [ite_eq_left hv]
    let r := primeRemainder p hp (a i) (supported_element_ne_zero _ (ha i))
    have hr := primeRemainder_supported p hp (a i) (ha i)
    have hcop : IsCoprime p r := hp.irreducible.coprime_iff_not_dvd.mpr
      (primeRemainder_spec p hp (a i) (supported_element_ne_zero _ (ha i))).2
    have hf : a i=p^(n+1)*r := by
      simpa only [hv] using (primeRemainder_spec p hp (a i) (supported_element_ne_zero _ (ha i))).1
    have he := central_error_shortening p r n hs hr hpp
      (primeRemainder_primary p hp hpp (a i) (ha i) (hap i)) hcop h
    have he' : gaussRow (a i) (ha i) h-gaussRow (a i) (ha i) (p^6*h) =
        primeRoot p (n+1)*(errorScalar p hp.ne_zero n h *
          (residualCharacter p (n+1) r*gaussRow r hr h)) := by
      have hh := (div_eq_iff (primeRoot_ne_zero p hp.ne_zero (n+1))).mp he
      simp only [hf,errorScalar]
      exact hh.trans (by ring)
    rw [he']
    ring
  · simp only [ite_eq_right hv,zero_mul,mul_zero]

theorem source_error_shortening (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (n : ℕ) (h : O) :
    amplificationError Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I : supportedColumns S => c I)
      (fun I => multiplicity p (sourceGenerator S I)) p (n+1) h =
      (primeRoot p (n+1)*errorScalar p hp.ne_zero n h)*
        gaussPolynomial Finset.univ
          (fun I : supportedColumns S => primeRemainder p hp (sourceGenerator S I)
            (supported_element_ne_zero _ (sourceGenerator_supported S I)))
          (fun I => primeRemainder_supported p hp (sourceGenerator S I) (sourceGenerator_supported S I))
          (fun I => if multiplicity p (sourceGenerator S I)=n+1 then
            c I*residualCharacter p (n+1)
              (primeRemainder p hp (sourceGenerator S I)
                (supported_element_ne_zero _ (sourceGenerator_supported S I))) else 0) h := by
  apply original_error_shortening _ _ _ _ _ p hp hs hpp n h
  intro I
  exact (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I
    (Finset.mem_filter.mp I.property).2)).2

end SevenEighths.CenteredMomentAmplificationSource

end

end OAI
