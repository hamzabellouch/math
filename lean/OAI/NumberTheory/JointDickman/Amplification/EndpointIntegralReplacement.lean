import OAI.NumberTheory.JointDickman.Probability.HistogramConjugation
import OAI.NumberTheory.JointDickman.Probability.HistogramIntegralIdentity

namespace OAI

/-! # The histogram error is the difference of the original endpoint integrals -/

namespace JointDickman
open Finset MeasureTheory
open scoped SchwartzMap

theorem endpoint_integral_replacement {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (hcut : q ≤ auxiliaryCutoff B)
    {a b N : ℝ} (ha : 0 < a) (hab : a ≤ b) (hN : 0 < N)
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (hg : ∀ x, |g x| ≤ 1) (hh : ∀ x, |h x| ≤ 1)
    (w₁ w₂ : ℝ → ℝ) {M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hw₁ : ∀ x, |w₁ x| ≤ M₁) (hw₂ : ∀ x, |w₂ x| ≤ M₂)
    (hs₁ : ∀ x, x ≤ a ∨ b < x → w₁ x = 0)
    (hs₂ : ∀ x, x ≤ a ∨ b < x → w₂ x = 0)
    (hl₁ : ∀ k ∈ primeSplitProductSupport (auxiliaryPrimes B), w₁ (k/N) ≠ 0 →
      Real.log k/B ∈ Set.Ioc (1/2 : ℝ) 3)
    (hl₂ : ∀ k ∈ primeSplitProductSupport (auxiliaryPrimes B), w₂ (k/N) ≠ 0 →
      Real.log k/B ∈ Set.Ioc (1/2 : ℝ) 3)
    (β : ℝ) (P : ZMod q → Prop) [DecidablePred P] (w : 𝓢(ℝ,ℝ)) :
    let J := histogramWindowCells (channelFineCount m B) (Real.log (a*N)/B) (Real.log (b*N)/B)
    let F := fun ξ => logOscillatoryTest w₁ B N (β*ξ)
    let G := fun ξ => logOscillatoryTest w₂ B N (-β*ξ)
    (∑ r : ZMod q, if P r then ∫ ξ : ℝ, testFourierTransform w ξ*
      (endpointFourierSum B a b N (subsetSiteTest (auxiliaryPrimes B) g) w₁
          (r.val/(q : ℝ)+β*ξ/N)*
        endpointFourierSum B a b N (subsetSiteTest (auxiliaryPrimes B) h) w₂
          (-(r.val/(q : ℝ)+β*ξ/N))) else 0)-
    (∑ r : ZMod q, if P r then ∫ ξ : ℝ, testFourierTransform w ξ*
      (sampledProjectedFourier m B q J g (fun i => F ξ (channelLower (channelFineCount m B) i)) r*
        sampledProjectedFourier m B q J h (fun i => G ξ (channelLower (channelFineCount m B) i)) (-r)) else 0) =
      manuscriptSampledIntegralError m B q J g h F G P w := by
  dsimp only
  let J := histogramWindowCells (channelFineCount m B) (Real.log (a*N)/B) (Real.log (b*N)/B)
  let F := fun ξ => logOscillatoryTest w₁ B N (β*ξ)
  let G := fun ξ => logOscillatoryTest w₂ B N (-β*ξ)
  have hid (ξ : ℝ) (r : ZMod q) :
      endpointFourierSum B a b N (subsetSiteTest (auxiliaryPrimes B) g) w₁
          (r.val/(q : ℝ)+β*ξ/N) = manuscriptFourier m B q J g (F ξ) r := by
    have he := endpointFourierSum_histogram (m := m) (B := B) (q := q) hm hB hcut ha hab hN g w₁ hs₁ hl₁ r (β*ξ/N)
    rw [div_mul_cancel₀ _ hN.ne'] at he
    exact he
  have hid' (ξ : ℝ) (r : ZMod q) :
      endpointFourierSum B a b N (subsetSiteTest (auxiliaryPrimes B) h) w₂
          (-(r.val/(q : ℝ)+β*ξ/N)) = manuscriptFourier m B q J h (G ξ) (-r) := by
    have he := endpointFourierSum_histogram_neg (m := m) (B := B) (q := q) hm hB hcut ha hab hN h w₂ hs₂ hl₂ r (β*ξ/N)
    rw [div_mul_cancel₀ _ hN.ne',← neg_mul] at he
    exact he
  simp_rw [hid,hid']
  symm
  exact manuscriptSampledIntegralError_eq J g h F G P w
    (fun r => (logarithmic_histogram_integrals hm hB J g h hg hh w₁ w₂ hM₁ hM₂ hw₁ hw₂ N β w r).1)
    (fun r => (logarithmic_histogram_integrals hm hB J g h hg hh w₁ w₂ hM₁ hM₂ hw₁ hw₂ N β w r).2)

end JointDickman

end OAI
