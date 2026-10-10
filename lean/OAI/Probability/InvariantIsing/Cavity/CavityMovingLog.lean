import OAI.Probability.InvariantIsing.Cavity.CavityMovingMoments
import OAI.Probability.InvariantIsing.Cavity.CavityUnflooredLog

namespace OAI

/-! Floor removal when both random normalizers vary. This is the form
needed for the finite system and its refining cascade approximation. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

theorem cavity_moving_unfloored_log
    {Ω Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (Ξ n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : (n : ℕ) → Measure (Ξ n)) [∀ n, IsProbabilityMeasure (Q n)]
    (Z : (n : ℕ) → Ω n → ℝ) (W : (n : ℕ) → Ξ n → ℝ)
    (hZ : ∀ n, Measurable (Z n)) (hW : ∀ n, Measurable (W n))
    {M K : ℝ} (hM : 1 ≤ M) (hK0 : 0 ≤ K)
    (hZ0 : ∀ n ω, 0 < Z n ω) (hW0 : ∀ n ω, 0 < W n ω)
    (hZM : ∀ n ω, Z n ω ≤ M) (hWM : ∀ n ω, W n ω ≤ M)
    (hiZ : ∀ n, Integrable (fun ω => (max (-Real.log (Z n ω)) 0)^2) (P n))
    (hiW : ∀ n, Integrable (fun ω => (max (-Real.log (W n ω)) 0)^2) (Q n))
    (hKZ : ∀ n, (∫ ω, (max (-Real.log (Z n ω)) 0)^2 ∂P n) ≤ K)
    (hKW : ∀ n, (∫ ω, (max (-Real.log (W n ω)) 0)^2 ∂Q n) ≤ K)
    (hfloors : ∀ δ > 0, Tendsto (fun n =>
      (∫ ω, Real.log (Z n ω + δ) ∂P n) - ∫ ω, Real.log (W n ω + δ) ∂Q n)
        atTop (𝓝 0)) :
    Tendsto (fun n => (∫ ω, Real.log (Z n ω) ∂P n) -
      ∫ ω, Real.log (W n ω) ∂Q n) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ₁, hδ₁, he₁⟩ := cavity_log_floor_uniform P Z hZ hZ0 hZM hM hK0 hiZ hKZ
    (ε / 3) (by positivity)
  obtain ⟨δ₂, hδ₂, he₂⟩ := cavity_log_floor_uniform Q W hW hW0 hWM hM hK0 hiW hKW
    (ε / 3) (by positivity)
  let δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have hclose := (hfloors δ hδ).eventually
    (Metric.ball_mem_nhds 0 (show 0 < ε / 3 by positivity))
  filter_upwards [hclose] with n hn
  rw [Real.dist_eq, sub_zero] at hn
  rw [Real.dist_eq, sub_zero]
  have h₁ := (he₁ δ ⟨hδ.le, min_le_left _ _⟩ n).2
  have h₂ := (he₂ δ ⟨hδ.le, min_le_right _ _⟩ n).2
  rw [← cavity_log_floor_mean_difference (P n) (Z n) (hZ n) (hZ0 n) (hZM n) hδ (hiZ n),
    abs_sub_comm] at h₁
  rw [← cavity_log_floor_mean_difference (Q n) (W n) (hW n) (hW0 n) (hWM n) hδ (hiW n)] at h₂
  have htri := abs_sub_le (∫ ω, Real.log (Z n ω) ∂P n)
    (∫ ω, Real.log (Z n ω + δ) ∂P n) (∫ ω, Real.log (W n ω) ∂Q n)
  have htri' := abs_sub_le (∫ ω, Real.log (Z n ω + δ) ∂P n)
    (∫ ω, Real.log (W n ω + δ) ∂Q n) (∫ ω, Real.log (W n ω) ∂Q n)
  linarith

theorem cavity_moving_log_of_moments
    {Ω Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (Ξ n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : (n : ℕ) → Measure (Ξ n)) [∀ n, IsProbabilityMeasure (Q n)]
    (Z : (n : ℕ) → Ω n → ℝ) (W : (n : ℕ) → Ξ n → ℝ)
    (hZ : ∀ n, Measurable (Z n)) (hW : ∀ n, Measurable (W n))
    {M K : ℝ} (hM : 1 ≤ M) (hK0 : 0 ≤ K)
    (hZ0 : ∀ n ω, 0 < Z n ω) (hW0 : ∀ n ω, 0 < W n ω)
    (hZM : ∀ n ω, Z n ω ≤ M) (hWM : ∀ n ω, W n ω ≤ M)
    (hiZ : ∀ n, Integrable (fun ω => (max (-Real.log (Z n ω)) 0)^2) (P n))
    (hiW : ∀ n, Integrable (fun ω => (max (-Real.log (W n ω)) 0)^2) (Q n))
    (hKZ : ∀ n, (∫ ω, (max (-Real.log (Z n ω)) 0)^2 ∂P n) ≤ K)
    (hKW : ∀ n, (∫ ω, (max (-Real.log (W n ω)) 0)^2 ∂Q n) ≤ K)
    (hmom : ∀ k : ℕ, Tendsto (fun n =>
      (∫ ω, Z n ω ^ k ∂P n) - ∫ ω, W n ω ^ k ∂Q n) atTop (𝓝 0)) :
    Tendsto (fun n => (∫ ω, Real.log (Z n ω) ∂P n) -
      ∫ ω, Real.log (W n ω) ∂Q n) atTop (𝓝 0) := by
  apply cavity_moving_unfloored_log P Q Z W hZ hW hM hK0 hZ0 hW0 hZM hWM hiZ hiW hKZ hKW
  intro δ hδ
  exact cavity_moving_floored_log P Q Z W hZ hW hδ
    (fun n ω => ⟨(hZ0 n ω).le, hZM n ω⟩) (fun n ω => ⟨(hW0 n ω).le, hWM n ω⟩) hmom

end InvariantIsing

end

end OAI
