import OAI.NumberTheory.DirichletL.Detector.GramPrimeSeparation

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcretePrimeRowBridge UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι]

theorem exists_nonexceptional_residue (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (hC : C≠0) (hk0 : k≠0) (u : Oˣ) (a b : ℕ) (r : O)
    (hr : Supported (Ideal.span {r})) (hk : k=u.val*goodLambda^a*(2:O)^b*r)
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,goodLambda∉P i) (c : ι→ℕ)
    (hc : ∀i,1≤c i) (hfac : Ideal.span {C}=∏i,P i^c i)
    (p : Id) [p.IsMaximal] (hp0 : p≠0) (hgp : goodLambda∉p)
    (hchar : ringChar (O⧸p)≠2) (hfixed : ¬p∣jointFixedModulus S hS) (hcommon : ¬p∣∏i,P i)
    (he : ¬6∣(normalizedFactors (Ideal.span {r})).count p) :
    ∃(M : Id)(hM : M≠0),
      Ideal.absNorm M≤Ideal.absNorm (jointFixedModulus S hS)*
        Ideal.absNorm (Ideal.span {C})*Ideal.absNorm (Ideal.span {k}) ∧
      letI : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient hM
      letI : Fintype (O⧸M):=Fintype.ofFinite _
      ∀d : O,∃A : (O⧸M)→(O⧸M)→ℂ,
        (∀n₁ n₂,A (Ideal.Quotient.mk M n₁) (Ideal.Quotient.mk M n₂)=
          jointExtension S hS σ C k u a b r hr P hg c (d*n₁) (d*n₂)) ∧
        (∀x y,‖A x y‖≤Ideal.absNorm (Ideal.span {C})) ∧
        (∑x,∑y,A x y)=0 := by
  obtain ⟨J,hJ,hcop,hJ0⟩ := exists_nonexceptional_separation (jointFixedModulus S hS)
    (∏i,P i) (Ideal.span {r}) p hr.1 hp0 hfixed hcommon
  let e := (normalizedFactors (Ideal.span {r})).count p
  let M : Id := (jointFixedModulus S hS*(∏i,P i)*J)*p^e
  have hMperiod : M=jointPeriod S hS P r := by
    rw [jointPeriod,hJ]
    dsimp [M,e]
    ring
  have hM0 : M≠0 := hMperiod ▸ jointPeriod_nonzero S hS C hC P c hc hfac r
    (CenteredMomentSupportedCorrelation.supported_element_ne_zero r hr)
  refine ⟨M,hM0,?_,?_⟩
  · rw [hMperiod]
    exact jointPeriod_norm_bound S hS C k hC hk0 u a b r hk P c hc hfac
  · let : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient hM0
    let : Fintype (O⧸M) := Fintype.ofFinite _
    let : Finite (O⧸jointFixedModulus S hS*(∏i,P i)*J) :=
      Ring.HasFiniteQuotients.finiteQuotient (left_ne_zero_of_mul hM0)
    let : Fintype (O⧸jointFixedModulus S hS*(∏i,P i)*J) := Fintype.ofFinite _
    let : Finite (O⧸p^e) := Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero _ hp0)
    let : Fintype (O⧸p^e) := Fintype.ofFinite _
    intro d
    let A : (O⧸M)→(O⧸M)→ℂ := fun x y=>
      jointExtension S hS σ C k u a b r hr P hg c (d*x.out) (d*y.out)
    refine ⟨A,?_,?_,?_⟩
    · intro n₁ n₂
      apply jointExtension_dilation_periodic
      · rw [←hMperiod]
        exact Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out (Ideal.Quotient.mk M n₁))
      · rw [←hMperiod]
        exact Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out (Ideal.Quotient.mk M n₂))
    · intro x y
      rw [hfac]
      exact jointExtension_norm S hS σ C k u a b r hr P hg c hc _ _
    · exact jointExtension_mean_zero S hS σ C k u a b r hr P hg c J p hgp hchar e he hJ hcop d

end SevenEighths.ProbeGramCommon
end

end OAI
