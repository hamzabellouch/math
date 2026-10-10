import OAI.Probability.InvariantIsing.Cavity.CavityReplicaFloor
import OAI.Probability.InvariantIsing.Cavity.CavityMovingMoments

namespace OAI

/-! Matching weighted moments determine unregularized bounded replica tests.
The uniform negative-log second moment controls small random normalizers. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

theorem cavity_moving_unregularized_ratio
    {Ω Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (Ξ n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : (n : ℕ) → Measure (Ξ n)) [∀ n, IsProbabilityMeasure (Q n)]
    (Z A : (n : ℕ) → Ω n → ℝ) (W D : (n : ℕ) → Ξ n → ℝ)
    (hZ : ∀ n, Measurable (Z n)) (hA : ∀ n, Measurable (A n))
    (hW : ∀ n, Measurable (W n)) (hD : ∀ n, Measurable (D n))
    {M K B : ℝ} (hM : 1 ≤ M) (hK : 0 ≤ K) (hB : 0 ≤ B) (r : ℕ)
    (hZ0 : ∀ n ω, 0 < Z n ω) (hW0 : ∀ n ω, 0 < W n ω)
    (hZM : ∀ n ω, Z n ω ≤ M) (hWM : ∀ n ω, W n ω ≤ M)
    (hAZ : ∀ n ω, |A n ω| ≤ B * Z n ω ^ r)
    (hDW : ∀ n ω, |D n ω| ≤ B * W n ω ^ r)
    (hiZ : ∀ n, Integrable (fun ω => (max (-Real.log (Z n ω)) 0)^2) (P n))
    (hiW : ∀ n, Integrable (fun ω => (max (-Real.log (W n ω)) 0)^2) (Q n))
    (hKZ : ∀ n, (∫ ω, (max (-Real.log (Z n ω)) 0)^2 ∂P n) ≤ K)
    (hKW : ∀ n, (∫ ω, (max (-Real.log (W n ω)) 0)^2 ∂Q n) ≤ K)
    (hreg : ∀ δ > 0, Tendsto (fun n =>
      (∫ ω, A n ω / (Z n ω + δ)^r ∂P n) -
        ∫ ω, D n ω / (W n ω + δ)^r ∂Q n) atTop (𝓝 0)) :
    Tendsto (fun n => (∫ ω, A n ω / Z n ω ^ r ∂P n) -
      ∫ ω, D n ω / W n ω ^ r ∂Q n) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ₁, hδ₁, hb₁⟩ := cavity_replica_floor_uniform P A Z hA hZ hM hB hK r
    hZ0 hZM hAZ hiZ hKZ (ε / 3) (by positivity)
  obtain ⟨δ₂, hδ₂, hb₂⟩ := cavity_replica_floor_uniform Q D W hD hW hM hB hK r
    hW0 hWM hDW hiW hKW (ε / 3) (by positivity)
  let δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have hclose := (hreg δ hδ).eventually
    (Metric.ball_mem_nhds 0 (show 0 < ε / 3 by positivity))
  filter_upwards [hclose] with n hn
  rw [Real.dist_eq, sub_zero] at hn ⊢
  have h₁ := hb₁ δ hδ (min_le_left _ _) n
  have h₂ := hb₂ δ hδ (min_le_right _ _) n
  have htri := abs_sub_le (∫ ω, A n ω / Z n ω ^ r ∂P n)
    (∫ ω, A n ω / (Z n ω + δ)^r ∂P n) (∫ ω, D n ω / W n ω ^ r ∂Q n)
  have htri' := abs_sub_le (∫ ω, A n ω / (Z n ω + δ)^r ∂P n)
    (∫ ω, D n ω / (W n ω + δ)^r ∂Q n) (∫ ω, D n ω / W n ω ^ r ∂Q n)
  rw [abs_sub_comm] at h₂
  linarith

theorem cavity_moving_ratio_of_moments
    {Ω Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (Ξ n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : (n : ℕ) → Measure (Ξ n)) [∀ n, IsProbabilityMeasure (Q n)]
    (Z A : (n : ℕ) → Ω n → ℝ) (W D : (n : ℕ) → Ξ n → ℝ)
    (hZ : ∀ n, Measurable (Z n)) (hA : ∀ n, Measurable (A n))
    (hW : ∀ n, Measurable (W n)) (hD : ∀ n, Measurable (D n))
    {M K B : ℝ} (hM : 1 ≤ M) (hK : 0 ≤ K) (hB : 0 ≤ B) (r : ℕ)
    (hZ0 : ∀ n ω, 0 < Z n ω) (hW0 : ∀ n ω, 0 < W n ω)
    (hZM : ∀ n ω, Z n ω ≤ M) (hWM : ∀ n ω, W n ω ≤ M)
    (hAZ : ∀ n ω, |A n ω| ≤ B * Z n ω ^ r)
    (hDW : ∀ n ω, |D n ω| ≤ B * W n ω ^ r)
    (hiZ : ∀ n, Integrable (fun ω => (max (-Real.log (Z n ω)) 0)^2) (P n))
    (hiW : ∀ n, Integrable (fun ω => (max (-Real.log (W n ω)) 0)^2) (Q n))
    (hKZ : ∀ n, (∫ ω, (max (-Real.log (Z n ω)) 0)^2 ∂P n) ≤ K)
    (hKW : ∀ n, (∫ ω, (max (-Real.log (W n ω)) 0)^2 ∂Q n) ≤ K)
    (hmom : ∀ k : ℕ, Tendsto (fun n =>
      (∫ ω, A n ω * Z n ω ^ k ∂P n) - ∫ ω, D n ω * W n ω ^ k ∂Q n)
        atTop (𝓝 0)) :
    Tendsto (fun n => (∫ ω, A n ω / Z n ω ^ r ∂P n) -
      ∫ ω, D n ω / W n ω ^ r ∂Q n) atTop (𝓝 0) := by
  apply cavity_moving_unregularized_ratio P Q Z A W D hZ hA hW hD hM hK hB r
    hZ0 hW0 hZM hWM hAZ hDW hiZ hiW hKZ hKW
  intro δ hδ
  have hc : ContinuousOn (fun z : ℝ => 1 / (z + δ)^r) (Icc 0 M) :=
    continuousOn_const.div ((continuousOn_id.add continuousOn_const).pow r)
      (fun z hz => pow_ne_zero _ (by linarith [hz.1]))
  have ht := cavity_moving_weighted_moments P Q Z A W D hZ hA hW hD
    (B := B * M^r) (by positivity)
    (fun n ω => ⟨(hZ0 n ω).le, hZM n ω⟩)
    (fun n ω => ⟨(hW0 n ω).le, hWM n ω⟩)
    (fun n ω => (hAZ n ω).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (hZ0 n ω).le (hZM n ω) r) hB))
    (fun n ω => (hDW n ω).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (hW0 n ω).le (hWM n ω) r) hB)) hmom _ hc
  simpa only [one_div, ← div_eq_mul_inv] using ht

end InvariantIsing

end

end OAI
