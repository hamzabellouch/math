import OAI.NumberTheory.DirichletL.Moments.FirstAssembly

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstFrequency
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentFirstNormalization CenteredMomentFirstReduced CenteredMomentFirstAssembly
open CenteredMomentFirstColumns CenteredMomentCommonSupport CenteredMomentSupportedCorrelation
open CenteredMomentPrimitive CenteredMomentGaussEnergy CenteredMomentChildAssembly CenteredMomentMobiusRegroup
open RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem normalized_dilated_frequency {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6)
    (e a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (har : IsCoprime a (b*finitePrimeModulus P)) (hbr : IsCoprime b (finitePrimeModulus P))
    (k : ℝ) (h : O) :
    let r := finitePrimeModulus P
    let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
    let ρ := finiteSexticRow P hg j
    tripleRow a b r (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ G e*
      ((k/‖eisEmbedding (a*(b*r))‖^2:ℝ):ℂ)*
      tripleFourier a b r (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
        (finitePrimeModulus_ne_zero P) (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ G h =
      ((k:ℂ)*canonicalNormalizedGauss P hcop hg j/(‖eisEmbedding r‖:ℂ))*star (ρ h)*
        originalPhase e r ρ a b*
        ((gaussRow a ha h/(‖eisEmbedding a‖:ℂ))*star (gaussRow b hb (-h)/(‖eisEmbedding b‖:ℂ))) := by
  dsimp only
  let := finite_quotient_span (supported_element_ne_zero b hb)
  have he := normalized_active_coefficient P hcop hg hchar j hj0 hj6 a b ha hb har hbr h
  dsimp only at he
  rw [Complex.ofReal_div]
  calc
    _ = (k:ℂ)*tripleRow a b (finitePrimeModulus P) (supportedModulusCharacter a ha)
        (supportedModulusCharacter b hb)⁻¹
        (principalSexticRow P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P)) e*
        (tripleFourier a b (finitePrimeModulus P) (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
          (finitePrimeModulus_ne_zero P) (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹
          (principalSexticRow P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P)) h /
          (‖eisEmbedding (a*(b*finitePrimeModulus P))‖^2:ℝ)) := by ring
    _ = _ := by
      rw [he,tripleRow,← MulChar.star_apply',supportedModulusCharacter_mk,
        supportedModulusCharacter_mk,
        principalSexticRow_mk P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P) e]
      simp only [originalPhase,Complex.star_def,map_div₀,Complex.conj_ofReal]
      ring

def dilatedFrequency {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i) (j : ι → ℕ)
    (e a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (k : ℝ) (h : O) : ℂ :=
  let r := finitePrimeModulus P
  let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
  tripleRow a b r (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ G e*
    ((k/‖eisEmbedding (a*(b*r))‖^2:ℝ):ℂ)*
    tripleFourier a b r (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
      (finitePrimeModulus_ne_zero P) (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ G h

theorem finite_dilated_children {ι α β : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6)
    (S : Finset α) (T : Finset β) (a : α → O) (b : β → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (hb : ∀ l,Supported (Ideal.span {b l}))
    (hpa : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣a i-1)
    (hpb : ∀ l,ConcretePrimeRowBridge.goodLambda^2∣b l-1)
    (har : ∀ i,IsCoprime (a i) (finitePrimeModulus P))
    (hbr : ∀ l,IsCoprime (b l) (finitePrimeModulus P))
    (c : α → ℂ) (d : β → ℂ) (e : O) (k : ℝ) (h : O) (K : α → β → ℂ) :
    let r := finitePrimeModulus P
    let ρ := finiteSexticRow P hg j
    (∑ i∈S,∑ l∈T,
      (if IsCoprime (a i) (b l) then dilatedFrequency P hcop hg j e (a i) (b l) (ha i) (hb l) k h else 0)*
        (c i*star (d l))*K i l) =
      ((k:ℂ)*canonicalNormalizedGauss P hcop hg j/(‖eisEmbedding r‖:ℂ))*star (ρ h)*
        ∑ L∈divisorPool T (fun l => Ideal.span {b l}),
          (UniqueFactorizationMonoid.moebius L:ℂ)*ρ e*
            ∑ χ : RayCharacter,∑ ξ : RayCharacter,pairCoeff firstPhaseTable χ ξ*
              ∑ i∈S,∑ l∈T,
                ((divisorCoefficient L a (fun i => (c i/(‖eisEmbedding (a i)‖:ℂ))*leftCoefficient e r ρ (a i)) χ i*
                    gaussRow (a i) (ha i) h)*
                  star (divisorCoefficient L b (fun l => (d l/(‖eisEmbedding (b l)‖:ℂ))*rightCoefficient e r ρ (b l)) (ξ⁻¹) l*
                    gaussRow (b l) (hb l) (-h)))*K i l := by
  dsimp only
  let r := finitePrimeModulus P
  let ρ := finiteSexticRow P hg j
  let F := ((k:ℂ)*canonicalNormalizedGauss P hcop hg j/(‖eisEmbedding r‖:ℂ))*star (ρ h)
  have ht (i : α) (l : β) :
      (if IsCoprime (a i) (b l) then dilatedFrequency P hcop hg j e (a i) (b l) (ha i) (hb l) k h else 0)*
          (c i*star (d l))*K i l =
        F*((if IsCoprime (a i) (b l) then originalPhase e r ρ (a i) (b l) else 0)*
          ((c i/(‖eisEmbedding (a i)‖:ℂ))*star (d l/(‖eisEmbedding (b l)‖:ℂ)))*
          (gaussRow (a i) (ha i) h*star (gaussRow (b l) (hb l) (-h)))*K i l) := by
    by_cases hab : IsCoprime (a i) (b l)
    · simp only [hab,ite_true]
      rw [show dilatedFrequency P hcop hg j e (a i) (b l) (ha i) (hb l) k h=_ from
        normalized_dilated_frequency P hcop hg hchar j hj0 hj6 e (a i) (b l) (ha i) (hb l)
          (hab.mul_right (har i)) (hbr l) k h]
      dsimp only [F,r,ρ]
      simp only [Complex.star_def,map_div₀,Complex.conj_ofReal]
      ring
    · simp [hab]
  simp_rw [ht,← Finset.mul_sum]
  rw [finite_first_children S T a b ha hb hpa hpb
    (fun i => c i/(‖eisEmbedding (a i)‖:ℂ)) (fun l => d l/(‖eisEmbedding (b l)‖:ℂ)) e r ρ
    (finiteSexticRow_mul P hg j) h K]

end SevenEighths.CenteredMomentFirstFrequency

end

end OAI
