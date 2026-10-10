import OAI.NumberTheory.JointDickman.Amplification.FrozenSmallArcIntegral
import OAI.NumberTheory.JointDickman.Amplification.ScaledFourierTail

namespace OAI

/-! # The published coefficient approximation with full Fourier inversion range -/

namespace JointDickman
open Filter MeasureTheory Function
open scoped Topology ArithmeticFunction.Moebius SchwartzMap

theorem coefficient_frozen_fullArc_integral_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ a b : ℝ, 0 < a → a ≤ b →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X →
      Real.log X ∈ Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B) →
      ∀ j : ℕ, ∀ (_ : NeZero j), ∀ Q : ℕ,
      ∀ (w : 𝓢(ℝ,ℝ)) (w' : ℝ → ℝ) (M N : ℝ), 0 ≤ M → 0 ≤ N →
      (∀ x, HasDerivAt w (w' x) x) → Continuous w' →
      (∀ x, |w x| ≤ M) → (∀ x, |w' x| ≤ N) →
      (∀ x, x ≤ a ∨ b < x → w x = 0) →
      ∀ F G : ℝ → ℂ, Continuous F → Continuous G → Periodic F 1 → Periodic G 1 →
      ∀ MF MG : ℝ, 0 ≤ MF → 0 ≤ MG → (∀ x, ‖F x‖ ≤ MF) → (∀ x, ‖G x‖ ≤ MG) →
      ‖(∫ x in smallMajorArcRegion B j X Q,
          F x*G x*smoothCoefficientAdditiveSum B X (-(j : ℝ)*x) w)-
        fullSmallMajorArcModel B j X Q (fun x => F x*G x) ((fun ξ => (coefficientDensity c H B (Real.log X/B) : ℂ)*testFourierTransform w ξ))
          (fun q => (μ (q : ℕ) : ℂ)/((q : ℕ).totient : ℂ))‖ ≤
        (X*((K*b*(2*M+(N+2*Real.pi*M)*(b-a)))*(B : ℝ)^(-50 : ℝ)+C*M/B))/2*
          ((∫ x in (0 : ℝ)..1, ‖F x‖^2)+(∫ x in (0 : ℝ)..1, ‖G x‖^2))+
        ((B^12 : ℕ) : ℝ)*((B^12 : ℕ)+1)*
          ((MF*MG)*(((B : ℝ)^13)^10)⁻¹*|coefficientDensity c H B (Real.log X/B)| *
            (∫ ξ : ℝ, |ξ|^10*‖testFourierTransform w ξ‖)) := by
  obtain ⟨c,hc,hcpos,H,K,hK,hsmall⟩ := coefficient_frozen_smallMajorArc_integral_law hSD hSW hM hMP
  refine ⟨c,hc,hcpos,H,K,hK,?_⟩
  intro a b ha hab
  obtain ⟨C,hC,hsmall⟩ := hsmall a b ha hab
  refine ⟨C,hC,?_⟩
  filter_upwards [hsmall,eventually_ge_atTop 1] with B hs hB
  intro X hX hlog j hj Q w w' M N hM0 hN0 hw hw' hwb hw'b hsupp F G hF hG hpF hpG
    MF MG hMF hMG hFb hGb
  let : NeZero j := hj
  have hBpos : 0 < B := by omega
  have he := hs X hX hlog j hj Q w w' M N hM0 hN0 hw hw' hwb hw'b hsupp F G hF hG hpF hpG
  have ht := frozen_model_tail_error (j := j) hBpos X Q (fun x => F x*G x) (hF.mul hG) w
    (coefficientDensity c H B (Real.log X/B))
    (fun q => (μ (q : ℕ) : ℂ)/((q : ℕ).totient : ℂ))
    (fun q => moebius_totient_complex_norm_le_one (q : ℕ))
    (mul_nonneg hMF hMG) (fun x => by
      rw [norm_mul]
      exact mul_le_mul (hFb x) (hGb x) (norm_nonneg _) hMF) 10
  rw [norm_sub_rev] at ht
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add he ht)

end JointDickman

end OAI
