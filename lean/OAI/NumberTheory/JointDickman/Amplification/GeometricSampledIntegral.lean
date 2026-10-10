import OAI.NumberTheory.JointDickman.Probability.GeometricHistogramErrors
import OAI.NumberTheory.JointDickman.Amplification.LogFrequencyBounds

namespace OAI

/-! # Summed replacement of the actual logarithmic endpoint integrals -/

namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology SchwartzMap

noncomputable def manuscriptSampledIntegralError (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B)))
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (F G : ℝ → ℝ → ℂ)
    (P : ZMod q → Prop) [DecidablePred P] (w : 𝓢(ℝ,ℝ)) : ℂ :=
  ∫ ξ : ℝ, testFourierTransform w ξ*
    (oppositeProductSum P (manuscriptFourier m B q J g (F ξ))
        (manuscriptFourier m B q J h (G ξ))-
      oppositeProductSum P
        (sampledProjectedFourier m B q J g (fun i => F ξ (channelLower (channelFineCount m B) i)))
        (sampledProjectedFourier m B q J h (fun i => G ξ (channelLower (channelFineCount m B) i))))

theorem geometric_sampled_integral_error_sum
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → ∀ᶠ B : ℕ in atTop,
      ∀ q : ℕ, [NeZero q] → q ≤ B → ∀ a b t : ℝ, 0 < a → a ≤ b → 0 < t →
      ∀ S : Finset ℤ, ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      ∀ (w₁ w₂ w₁' w₂' : ℝ → ℝ) (M₁ M₂ D₁ D₂ β : ℝ),
      0 ≤ M₁ → 0 ≤ M₂ → 0 ≤ D₁ → 0 ≤ D₂ →
      (∀ x, HasDerivAt w₁ (w₁' x) x) → (∀ x, HasDerivAt w₂ (w₂' x) x) →
      (∀ x, |w₁ x| ≤ M₁) → (∀ x, |w₂ x| ≤ M₂) →
      (∀ x, |w₁' x| ≤ D₁) → (∀ x, |w₂' x| ≤ D₂) →
      ∀ (P : ZMod q → Prop) [DecidablePred P], ∀ w : 𝓢(ℝ,ℝ),
      let J := geometricHistogramWindow m B t (Real.log a) (Real.log b)
      let F := fun k ξ => logOscillatoryTest w₁ B (Real.exp ((k : ℝ)*t)) (β*ξ)
      let G := fun k ξ => logOscillatoryTest w₂ B (Real.exp ((k : ℝ)*t)) (-β*ξ)
      let L₁ := (D₁+2*Real.pi*|β| * M₁)*((B : ℝ)*(b*Real.exp 1))
      let L₂ := (D₂+2*Real.pi*|β| * M₂)*((B : ℝ)*(b*Real.exp 1))
      (∑ k ∈ S, ‖manuscriptSampledIntegralError m B q (J k) g h (F k) (G k) P w‖) ≤
        ((q : ℝ)/(q.totient : ℝ))*((Real.log b-Real.log a+2)/B)*C*
          ((1+Real.log b-Real.log a)/t+1)*
          (2*channelMesh (channelFineCount m B)*(L₁*M₂+M₁*L₂)+
            2*M₁*M₂*(B : ℝ)^(-(1/80 : ℝ)))*
          (∫ ξ : ℝ, ‖testFourierTransform w ξ‖*(1+|ξ|)) := by
  obtain ⟨C,hC,hmajorant⟩ := geometric_histogram_error_sum hSD hSW hM hMP
  refine ⟨C,hC,?_⟩
  intro m hm
  filter_upwards [hmajorant m hm,eventually_ge_atTop 1] with B hmajor hB
  intro q _ hq a b t ha hab ht S g h hg hh w₁ w₂ w₁' w₂' M₁ M₂ D₁ D₂ β
    hM₁ hM₂ hD₁ hD₂ hw₁ hw₂ hwb₁ hwb₂ hwd₁ hwd₂ P _ w
  dsimp only
  let J := geometricHistogramWindow m B t (Real.log a) (Real.log b)
  let F := fun k ξ => logOscillatoryTest w₁ B (Real.exp ((k : ℝ)*t)) (β*ξ)
  let G := fun k ξ => logOscillatoryTest w₂ B (Real.exp ((k : ℝ)*t)) (-β*ξ)
  let L₁ := (D₁+2*Real.pi*|β| * M₁)*((B : ℝ)*(b*Real.exp 1))
  let L₂ := (D₂+2*Real.pi*|β| * M₂)*((B : ℝ)*(b*Real.exp 1))
  let A := fun k => manuscriptAmplitudeEnergy m B q (J k)
  let R := fun k => manuscriptResidueEnergy m B q (J k) g
  let T := fun k => manuscriptResidueEnergy m B q (J k) h
  let E := fun k => 2*A k*channelMesh (channelFineCount m B)*(L₁*M₂+M₁*L₂)+
    M₁*M₂*(Real.sqrt (R k)*Real.sqrt (A k)+Real.sqrt (A k)*Real.sqrt (T k))
  let W := ∫ ξ : ℝ, ‖testFourierTransform w ξ‖*(1+|ξ|)
  have hW : 0 ≤ W := integral_nonneg (fun ξ => by positivity)
  have hb := ha.trans_le hab
  have hBpos : 0 < B := by omega
  have hJ (k : ℤ) : J k = histogramWindowCells (channelFineCount m B)
      (Real.log (a*Real.exp ((k : ℝ)*t))/B) (Real.log (b*Real.exp ((k : ℝ)*t))/B) := by
    simp only [J,geometricHistogramWindow,Real.log_mul ha.ne' (Real.exp_ne_zero _),
      Real.log_mul hb.ne' (Real.exp_ne_zero _),Real.log_exp]
    congr 2 <;> ring
  have hlocal (k : ℤ) :
      ‖manuscriptSampledIntegralError m B q (J k) g h (F k) (G k) P w‖ ≤ E k*W := by
    obtain ⟨hf,hi,hl⟩ := logOscillatoryTest_frequency_bounds (a := a) hm hB hb
      (Real.exp_pos ((k : ℝ)*t)) hM₁ hD₁ w₁ w₁' hw₁ hwb₁ hwd₁ β
    obtain ⟨hf',hi',hl'⟩ := logOscillatoryTest_frequency_bounds (a := a) hm hB hb
      (Real.exp_pos ((k : ℝ)*t)) hM₂ hD₂ w₂ w₂' hw₂ hwb₂ hwd₂ (-β)
    rw [← hJ k] at hf hi hl hf' hi' hl'
    simp only [abs_neg] at hl'
    have he := manuscript_to_sampled_integral_error hm hBpos (J k) (J k) g h hg hh
      (F k) (G k) (show 0 ≤ M₁ from hM₁) (show 0 ≤ M₂ from hM₂)
      (show 0 ≤ L₁ by dsimp [L₁]; positivity) (show 0 ≤ L₂ by dsimp [L₂]; positivity)
      hf hf' hi hi' hl hl' P w
    have hs : Real.sqrt (A k)*Real.sqrt (A k) = A k := by
      nlinarith [Real.sq_sqrt (manuscriptAmplitudeEnergy_nonneg (q := q) hm hBpos (J k))]
    refine he.trans_eq ?_
    change (2*Real.sqrt (A k)*Real.sqrt (A k)*channelMesh (channelFineCount m B)*(L₁*M₂+M₁*L₂)+
      M₁*M₂*(Real.sqrt (R k)*Real.sqrt (A k)+Real.sqrt (A k)*Real.sqrt (T k)))*W = E k*W
    dsimp [E]
    rw [mul_assoc 2 (Real.sqrt (A k)),hs]
  have he := hmajor q hq t (Real.log a) (Real.log b) ht (Real.log_le_log ha hab) S
    g h hg hh M₁ M₂ L₁ L₂ hM₁ hM₂ (by dsimp [L₁]; positivity) (by dsimp [L₂]; positivity)
  calc
    _ ≤ ∑ k ∈ S, E k*W := sum_le_sum (fun k _ => hlocal k)
    _ = (∑ k ∈ S, E k)*W := (sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right he hW

end JointDickman

end OAI
