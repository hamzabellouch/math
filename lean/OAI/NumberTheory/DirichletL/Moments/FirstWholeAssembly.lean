import OAI.NumberTheory.DirichletL.Moments.FirstWholeKernel

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstWholeAssembly
open ActualEisensteinCubic ConcreteTraceCRT CanonicalQuadraticSieve EisensteinSchwartzPoisson
open CenteredMomentFirstFrequency CenteredMomentFirstColumns CenteredMomentGaussEnergy
open CenteredMomentFirstAssembly CenteredMomentCommonSupport CenteredMomentFirstReduced
open CenteredMomentPrimitive CenteredMomentScale CenteredMomentSmooth CenteredMomentFirstWholeKernel
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

 theorem finite_whole_children {ι α β : Type*} [Fintype ι]
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
    (c : α → ℂ) (d : β → ℂ) (e : O) (k : ℝ) (hk : 0<k) (h : O) (hh : h≠0)
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ) (K₀ H₀ A₀ B₀ : ℝ)
    (hK₀ : 0<K₀) (hH₀ : 0<H₀) (hA₀ : 0<A₀) (hB₀ : 0<B₀) :
    let r := finitePrimeModulus P
    let ρ := finiteSexticRow P hg j
    let kr := k/‖eisEmbedding r‖^2
    (∑ i∈S,∑ l∈T,
      (if IsCoprime (a i) (b l) then dilatedFrequency P hcop hg j e (a i) (b l) (ha i) (hb l) k h else 0)*
        (c i*star (d l))*
        windows V kr (‖eisEmbedding h‖^2) (‖eisEmbedding (a i)‖^2) (‖eisEmbedding (b l)‖^2) K₀ H₀ A₀ B₀*
        paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (a i*(b l*r))‖^2)) =
      ((k:ℂ)*canonicalNormalizedGauss P hcop hg j/
        ((‖eisEmbedding r‖:ℂ)*(Real.sqrt A₀:ℂ)*(Real.sqrt B₀:ℂ)))*star (ρ h)*
        ∑ L∈divisorPool T (fun l => Ideal.span {b l}),
          (UniqueFactorizationMonoid.moebius L:ℂ)*ρ e*
            ∑ χ : RayCharacter,∑ ξ : RayCharacter,pairCoeff firstPhaseTable χ ξ*
              ∑ i∈S,∑ l∈T,
                ((divisorCoefficient L a (fun i => c i*leftCoefficient e r ρ (a i)) χ i*
                    gaussRow (a i) (ha i) h)*
                  star (divisorCoefficient L b (fun l => d l*rightCoefficient e r ρ (b l)) (ξ⁻¹) l*
                    gaussRow (b l) (hb l) (-h)))*
                wholeKernel W V (K₀*H₀/(A₀*B₀))
                  (Real.log (kr/K₀)) (Real.log (‖eisEmbedding h‖^2/H₀))
                  (Real.log (‖eisEmbedding (a i)‖^2/A₀)) (Real.log (‖eisEmbedding (b l)‖^2/B₀)) := by
  dsimp only
  let r := finitePrimeModulus P
  let ρ := finiteSexticRow P hg j
  let kr := k/‖eisEmbedding r‖^2
  let F := ((k:ℂ)*canonicalNormalizedGauss P hcop hg j/
    ((‖eisEmbedding r‖:ℂ)*(Real.sqrt A₀:ℂ)*(Real.sqrt B₀:ℂ)))*star (ρ h)
  let KK := fun i l => wholeKernel W V (K₀*H₀/(A₀*B₀))
    (Real.log (kr/K₀)) (Real.log (‖eisEmbedding h‖^2/H₀))
    (Real.log (‖eisEmbedding (a i)‖^2/A₀)) (Real.log (‖eisEmbedding (b l)‖^2/B₀))
  have ht (i : α) (l : β) :
      (if IsCoprime (a i) (b l) then dilatedFrequency P hcop hg j e (a i) (b l) (ha i) (hb l) k h else 0)*
        (c i*star (d l))*
        windows V kr (‖eisEmbedding h‖^2) (‖eisEmbedding (a i)‖^2) (‖eisEmbedding (b l)‖^2) K₀ H₀ A₀ B₀*
        paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (a i*(b l*r))‖^2) =
      F*((if IsCoprime (a i) (b l) then originalPhase e r ρ (a i) (b l) else 0)*(c i*star (d l)))*
        (gaussRow (a i) (ha i) h*star (gaussRow (b l) (hb l) (-h)))*KK i l := by
    by_cases hab : IsCoprime (a i) (b l)
    · simp only [hab,ite_true]
      have hh' := dilated_frequency_whole_kernel P hcop hg hchar j hj0 hj6 e
        (a i) (b l) (ha i) (hb l) (hab.mul_right (har i)) (hbr l) k hk h hh
        W V K₀ H₀ A₀ B₀ hK₀ hH₀ hA₀ hB₀
      dsimp only at hh'
      calc
        _ = (c i*star (d l))*(dilatedFrequency P hcop hg j e (a i) (b l) (ha i) (hb l) k h*
          windows V kr (‖eisEmbedding h‖^2) (‖eisEmbedding (a i)‖^2) (‖eisEmbedding (b l)‖^2) K₀ H₀ A₀ B₀*
          paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (a i*(b l*r))‖^2)) := by ring
        _ = _ := by rw [hh'];dsimp only [F,KK,kr,r,ρ];ring
    · simp [hab]
  calc
    _ = F*(∑ i∈S,∑ l∈T,
      ((if IsCoprime (a i) (b l) then originalPhase e r ρ (a i) (b l) else 0)*(c i*star (d l)))*
        (gaussRow (a i) (ha i) h*star (gaussRow (b l) (hb l) (-h)))*KK i l) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro l hl
      simpa only [mul_assoc] using ht i l
    _ = _ := congrArg (fun z => F*z)
      (finite_first_children S T a b ha hb hpa hpb c d e r ρ (finiteSexticRow_mul P hg j) h KK)

end SevenEighths.CenteredMomentFirstWholeAssembly

end

end OAI
