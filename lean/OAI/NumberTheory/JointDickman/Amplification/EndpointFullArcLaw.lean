import OAI.NumberTheory.JointDickman.Amplification.FrozenFullArcIntegral
import OAI.NumberTheory.JointDickman.Amplification.EndpointFourierReflection
import OAI.NumberTheory.JointDickman.Probability.SignedChannelMass

namespace OAI

/-! # The full-arc coefficient law with the actual endpoint sums -/

namespace JointDickman
open Finset Filter MeasureTheory Function
open scoped Topology SchwartzMap ArithmeticFunction.Moebius

theorem endpointFourierSum_periodic (B : ℕ) (a b N : ℝ)
    (g : Finset ℕ → ℝ) (w : ℝ → ℝ) :
    Periodic (endpointFourierSum B a b N g w) 1 := finiteAdditiveSum_periodic _ _

theorem endpointFourierSum_negative_periodic (B : ℕ) (a b N : ℝ)
    (g : Finset ℕ → ℝ) (w : ℝ → ℝ) :
    Periodic (fun θ => endpointFourierSum B a b N g w (-θ)) 1 := by
  intro θ
  change finiteAdditiveSum _ _ (-(θ+1)) = finiteAdditiveSum _ _ (-θ)
  have he : -(θ+1) = -θ+((-1 : ℤ) : ℝ) := by push_cast; ring
  rw [he,finiteAdditiveSum_add_int]

theorem endpoint_fullArc_coefficient_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {a b l u : ℝ} (ha : 0 < a) (hab : a ≤ b) (hl : 0 < l) (hlu : l ≤ u) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K C C₁ C₂ : ℝ, 0 ≤ K ∧ 0 ≤ C ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      ∀ᶠ B : ℕ in atTop, ∀ T X : ℝ, 0 < T → 0 < X →
      Real.log X ∈ Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B) →
      Real.log (T*X) ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B) →
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ,
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      ∀ (w₁ w₂ : ℝ → ℝ) (w : 𝓢(ℝ,ℝ)) (w' : ℝ → ℝ) (M M₀ D₀ : ℝ),
      0 ≤ M → 0 ≤ M₀ → 0 ≤ D₀ →
      (∀ x, |w₁ x| ≤ M) → (∀ x, |w₂ x| ≤ M) →
      (∀ x, HasDerivAt w (w' x) x) → Continuous w' →
      (∀ x, |w x| ≤ M₀) → (∀ x, |w' x| ≤ D₀) →
      (∀ x, x ≤ l ∨ u < x → w x = 0) →
      let F := endpointFourierSum B a b (T*X) (subsetSiteTest (auxiliaryPrimes B) g) w₁
      let G := fun θ => endpointFourierSum B a b (T*X) (subsetSiteTest (auxiliaryPrimes B) h) w₂ (-θ)
      ‖(∫ θ in smallMajorArcRegion B j X Q,
          F θ*G θ*smoothCoefficientAdditiveSum B X (-(j : ℝ)*θ) w)-
        fullSmallMajorArcModel B j X Q (fun θ => F θ*G θ)
          (fun ξ => (coefficientDensity c H B (Real.log X/B) : ℂ)*testFourierTransform w ξ)
          (fun q => (μ (q : ℕ) : ℂ)/((q : ℕ).totient : ℂ))‖ ≤
        (X*((K*u*(2*M₀+(D₀+2*Real.pi*M₀)*(u-l)))*(B : ℝ)^(-50 : ℝ)+C*M₀/B))*
          (C₂*M^2*(B : ℝ)^(-(3/2 : ℝ))/(T*X))+
        ((B^12 : ℕ) : ℝ)*((B^12 : ℕ)+1)*
          (((C₁*M/B)^2)*(((B : ℝ)^13)^10)⁻¹*|coefficientDensity c H B (Real.log X/B)| *
            (∫ ξ : ℝ, |ξ|^10*‖testFourierTransform w ξ‖)) := by
  obtain ⟨c,hc,hcpos,H,K,hK,he⟩ := coefficient_frozen_fullArc_integral_law hSD hSW hM hMP
  obtain ⟨C,hC,hcoef⟩ := he l u hl hlu
  obtain ⟨C₁,C₂,hC₁,hC₂,hmom⟩ := endpoint_fourier_moments hSD hM hMP ha hab
    (by norm_num : (0 : ℝ) < 1/4)
  refine ⟨c,hc,hcpos,H,K,C,C₁,C₂,hK,hC,hC₁,hC₂,?_⟩
  filter_upwards [hcoef,hmom,eventually_ge_atTop 1] with B hcB hmB hB
  intro T X hT hX hlogX hlogN j _ Q g h hg hh w₁ w₂ w w' M M₀ D₀ hM0 hM₀ hD₀
    hw₁ hw₂ hw hw' hwb hwd hsupp
  dsimp only
  let F := endpointFourierSum B a b (T*X) (subsetSiteTest (auxiliaryPrimes B) g) w₁
  let G := fun θ => endpointFourierSum B a b (T*X) (subsetSiteTest (auxiliaryPrimes B) h) w₂ (-θ)
  have hf := hmB (T*X) (mul_pos hT hX) hlogN.1 hlogN.2 (subsetSiteTest (auxiliaryPrimes B) g) (fun _ _ => hg _) w₁ M hM0 hw₁
  have hh' := hmB (T*X) (mul_pos hT hX) hlogN.1 hlogN.2 (subsetSiteTest (auxiliaryPrimes B) h) (fun _ _ => hh _) w₂ M hM0 hw₂
  norm_num only [show (-7/4+(1/4 : ℝ)) = -3/2 by norm_num] at hf hh'
  have hGint : (∫ θ in (0 : ℝ)..1, ‖G θ‖^2) ≤ C₂*M^2*(B : ℝ)^(-(3/2 : ℝ))/(T*X) := by
    simpa only [G,endpointFourierSum_neg_norm] using hh'.2
  have hFb : ∀ θ, ‖F θ‖ ≤ C₁*M/B := hf.1
  have hGb : ∀ θ, ‖G θ‖ ≤ C₁*M/B := fun θ => hh'.1 (-θ)
  have hF : Continuous F := endpointFourierSum_continuous _ _ _ _ _ _
  have hG : Continuous G := (endpointFourierSum_continuous _ _ _ _ _ _).comp continuous_neg
  have hP : 0 ≤ X*((K*u*(2*M₀+(D₀+2*Real.pi*M₀)*(u-l)))*(B : ℝ)^(-50 : ℝ)+C*M₀/B) := by
    have hu := hl.trans_le hlu
    positivity
  have he' := hcB X hX hlogX j inferInstance Q w w' M₀ D₀ hM₀ hD₀ hw hw' hwb hwd hsupp
    F G hF hG (endpointFourierSum_periodic _ _ _ _ _ _) (endpointFourierSum_negative_periodic _ _ _ _ _ _)
    (C₁*M/B) (C₁*M/B) (by positivity) (by positivity) hFb hGb
  refine he'.trans ?_
  apply add_le_add
  · exact (mul_le_mul_of_nonneg_left (add_le_add hf.2 hGint) (div_nonneg hP (by norm_num))).trans_eq (by ring)
  · exact le_of_eq (by ring)

end JointDickman

end OAI
