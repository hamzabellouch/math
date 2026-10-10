import OAI.NumberTheory.JointDickman.Amplification.FullArcDenominators
import OAI.NumberTheory.JointDickman.Amplification.EndpointIntegralReplacement
import OAI.NumberTheory.JointDickman.Probability.LogSampledKernel

namespace OAI

/-! # Exact connection of the coefficient arc model to the sampled log kernel -/

namespace JointDickman
open Finset MeasureTheory
open scoped SchwartzMap ArithmeticFunction.Moebius

theorem endpoint_full_model_replacement {m B j Q : ℕ} [NeZero j]
    (hm : 0 < m) (hB : 0 < B) (hQ : Q ≤ B^12) (hcut : j*Q ≤ auxiliaryCutoff B)
    {a b N X : ℝ} (ha : 0 < a) (hab : a ≤ b) (hN : 0 < N) (hX : 0 < X)
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
    (w : 𝓢(ℝ,ℝ)) (c : ℂ) :
    let J := histogramWindowCells (channelFineCount m B) (Real.log (a*N)/B) (Real.log (b*N)/B)
    let β := N/((j : ℝ)*X)
    let F := fun ξ => logOscillatoryTest w₁ B N (β*ξ)
    let G := fun ξ => logOscillatoryTest w₂ B N (-β*ξ)
    fullSmallMajorArcModel B j X Q
      (fun θ => endpointFourierSum B a b N (subsetSiteTest (auxiliaryPrimes B) g) w₁ θ*
        endpointFourierSum B a b N (subsetSiteTest (auxiliaryPrimes B) h) w₂ (-θ))
      (fun ξ => c*testFourierTransform w ξ) (fun q => (μ (q : ℕ) : ℂ)/((q : ℕ).totient : ℂ))-
      (c/j)*sampledEndpointKernel m B j Q J g h w₁ w₂ N β w =
      (c/j)*∑ q ∈ positiveDenominators Q, ((μ (q : ℕ) : ℂ)/((q : ℕ).totient : ℂ))*
        manuscriptSampledIntegralError m B (j*(q : ℕ)) J g h F G
          (fun r => r.val.Coprime (q : ℕ)) w := by
  dsimp only
  let J := histogramWindowCells (channelFineCount m B) (Real.log (a*N)/B) (Real.log (b*N)/B)
  let β := N/((j : ℝ)*X)
  let F := fun ξ => logOscillatoryTest w₁ B N (β*ξ)
  let G := fun ξ => logOscillatoryTest w₂ B N (-β*ξ)
  rw [fullSmallMajorArcModel_scalar_denominators hQ,sampledEndpointKernel_eq,
    ← mul_sub,← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro q hq
  rw [← mul_sub]
  congr 1
  have hd : j*(q : ℕ) ≤ auxiliaryCutoff B :=
    (Nat.mul_le_mul_left j ((mem_positiveDenominators Q q).mp hq)).trans hcut
  have he := endpoint_integral_replacement (m := m) (q := j*(q : ℕ)) hm hB hd
    ha hab hN g h hg hh w₁ w₂ hM₁ hM₂ hw₁ hw₂ hs₁ hs₂ hl₁ hl₂ β
    (fun r => r.val.Coprime (q : ℕ)) w
  have hfreq (ξ : ℝ) : β*ξ/N = ξ/((j : ℝ)*X) := by
    dsimp [β]
    field_simp
  simp only [hfreq] at he
  exact he

end JointDickman

end OAI
