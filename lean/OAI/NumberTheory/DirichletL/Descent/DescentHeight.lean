import OAI.NumberTheory.DirichletL.Descent.DescentProfiles

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation EisensteinSchwartzPoisson
noncomputable section

theorem frequencyTwist_fourier_moment (J : ℕ) (g : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : ℝ,
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖(𝓕 (frequencyTwist g θ)) t‖) ≤
        C * (1 + ‖θ‖)^(J + (volume : Measure ℝ).integrablePower) := by
  let K := J + (volume : Measure ℝ).integrablePower
  let D := twistSourceBound g K
  have hD : 0 ≤ D := twistSourceBound_nonneg g K
  let C := (2 : ℝ)^J * (coefficientMomentBound 0 D + coefficientMomentBound J D)
  have hC : 0 ≤ C := mul_nonneg (by positivity) (add_nonneg
    (coefficientMomentBound_nonneg 0 D hD) (coefficientMomentBound_nonneg J D hD))
  refine ⟨C, hC, ?_⟩
  intro θ
  let H := (1 + ‖θ‖)^K
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hs : ∀ i ≤ K,
      (SchwartzMap.seminorm ℝ 0 i) (frequencyTwist g θ) +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) (frequencyTwist g θ) ≤ D * H := by
    intro i hi
    exact (source_le_profileSourceBound (frequencyTwist g θ) K i hi).trans
      (profileSourceBound_frequencyTwist g θ K)
  have hh := uniform_fourier_one_plus_moment (frequencyTwist g θ) J 1 (D * H)
    (by norm_num) (mul_nonneg hD hH) (fun i hi => by simpa only [one_mul] using hs i hi)
  have hlin (j : ℕ) : coefficientMomentBound j (D * H) = coefficientMomentBound j D * H := by
    unfold coefficientMomentBound
    ring
  simpa only [one_mul, hlin, add_mul, C, H, K, mul_assoc, mul_add] using hh

theorem twisted_descent_profile_separation {ι : Type*} [Fintype ι]
    (g₁ g₂ Φ : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a₁ a₂ ak M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i)
    (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      ∀ θ₁ θ₂ : ℝ,
      (∀ y : ι → ℝ,
        (∏ i, V i (y i)) * frequencyTwist g₁ θ₁ (∑ i, a₁ i * y i) *
          frequencyTwist g₂ θ₂ (∑ i, a₂ i * y i) *
          paperRadialFourier Φ (R * Real.exp (∑ i, ak i * y i)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          tripleCoefficient (𝓕 (frequencyTwist g₁ θ₁)) (𝓕 (frequencyTwist g₂ θ₂)) b₃ (t₁,t₂,t₃) *
            (∏ i, V i (y i) * logPhase t₁ (a₁ i * y i) *
              logPhase t₂ (a₂ i * y i) * logPhase t₃ (ak i * y i))) ∧
      Integrable (fun t : Frequency =>
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient (𝓕 (frequencyTwist g₁ θ₁)) (𝓕 (frequencyTwist g₂ θ₂)) b₃ t‖) ∧
      (1 + R)^A * (∫ t : Frequency,
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient (𝓕 (frequencyTwist g₁ θ₁)) (𝓕 (frequencyTwist g₂ θ₂)) b₃ t‖) ≤
        C * (1 + ‖θ₁‖)^(J + (volume : Measure ℝ).integrablePower) *
          (1 + ‖θ₂‖)^(J + (volume : Measure ℝ).integrablePower) := by
  obtain ⟨Ck, hCk, hk⟩ := paperRadialFourier_log_separation_envelope Φ V ak M hM hV A J
  obtain ⟨C₁, hC₁, h₁⟩ := frequencyTwist_fourier_moment J g₁
  obtain ⟨C₂, hC₂, h₂⟩ := frequencyTwist_fourier_moment J g₂
  refine ⟨C₁ * C₂ * Ck, by positivity, ?_⟩
  intro R hR
  obtain ⟨b₃, he, hi, hb, hp⟩ := hk R hR
  refine ⟨b₃, ?_⟩
  intro θ₁ θ₂
  refine ⟨descent_profile_identity _ _ Φ V a₁ a₂ ak R b₃ he,
    tripleCoefficient_weighted_integrable _ _ _ J, ?_⟩
  rw [tripleCoefficient_weighted_integral]
  have hh := mul_le_mul (mul_le_mul (h₁ θ₁) (h₂ θ₂)
    (integral_nonneg (fun t => by positivity)) (by positivity)) hb
    (by positivity : 0 ≤ (1 + R)^A * ∫ t : ℝ, (1 + ‖t‖)^J * ‖b₃ t‖) (by positivity)
  convert hh using 1 <;> ring

end
end SevenEighths.InverseMoment

end OAI
