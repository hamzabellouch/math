import OAI.Probability.InvariantIsing.Cavity.CavityLogFloor

namespace OAI

/-! Removing the positive floor after the bounded finite-replica passage.
Only the second moment of the negative logarithm is used. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

lemma cavity_log_integrable_of_negative_sq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → ℝ) (hZ : Measurable Z)
    {M : ℝ} (hZ0 : ∀ ω, 0 < Z ω) (hZM : ∀ ω, Z ω ≤ M)
    (hi : Integrable (fun ω => (max (-Real.log (Z ω)) 0)^2) P) :
    Integrable (fun ω => Real.log (Z ω)) P := by
  apply ((integrable_const (1 + |Real.log M|)).add hi).mono' hZ.log.aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    change |Real.log (Z ω)| ≤ 1 + |Real.log M| + (max (-Real.log (Z ω)) 0)^2
    have hy := le_max_left (-Real.log (Z ω)) 0
    have hs := sq_nonneg (max (-Real.log (Z ω)) 0 - 1)
    have hu := Real.log_le_log (hZ0 ω) (hZM ω)
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (max (-Real.log (Z ω)) 0), abs_nonneg (Real.log M),
      le_abs_self (Real.log M)]

lemma cavity_floored_log_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → ℝ) (hZ : Measurable Z)
    {M δ : ℝ} (hZ0 : ∀ ω, 0 < Z ω) (hZM : ∀ ω, Z ω ≤ M) (hδ : 0 < δ) :
    Integrable (fun ω => Real.log (Z ω + δ)) P := by
  apply integrable_of_measurable_abs_le ((hZ.add_const δ).log)
    (c := |Real.log δ| + |Real.log (M + δ)|)
  intro ω
  have hl := Real.log_le_log hδ (show δ ≤ Z ω + δ by linarith [hZ0 ω])
  have hu := Real.log_le_log (show 0 < Z ω + δ by linarith [hZ0 ω])
    (show Z ω + δ ≤ M + δ by linarith [hZM ω])
  apply abs_le.mpr
  constructor <;> linarith [neg_abs_le (Real.log δ), le_abs_self (Real.log (M + δ)),
    abs_nonneg (Real.log δ), abs_nonneg (Real.log (M + δ))]

lemma cavity_log_floor_mean_difference {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → ℝ) (hZ : Measurable Z)
    {M δ : ℝ} (hZ0 : ∀ ω, 0 < Z ω) (hZM : ∀ ω, Z ω ≤ M) (hδ : 0 < δ)
    (hi : Integrable (fun ω => (max (-Real.log (Z ω)) 0)^2) P) :
    |(∫ ω, Real.log (Z ω + δ) ∂P) - ∫ ω, Real.log (Z ω) ∂P| =
      ∫ ω, Real.log (Z ω + δ) - Real.log (Z ω) ∂P := by
  rw [← integral_sub (cavity_floored_log_integrable P Z hZ hZ0 hZM hδ)
    (cavity_log_integrable_of_negative_sq P Z hZ hZ0 hZM hi)]
  exact abs_of_nonneg (integral_nonneg (fun ω => sub_nonneg.mpr
    (Real.log_le_log (hZ0 ω) (by linarith))))

theorem cavity_unfloored_log_tendsto
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {Ω₀ : Type*} [MeasurableSpace Ω₀]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : Measure Ω₀) [IsProbabilityMeasure Q]
    (Z : (n : ℕ) → Ω n → ℝ) (W : Ω₀ → ℝ)
    (hZ : ∀ n, Measurable (Z n)) (hW : Measurable W)
    {M K : ℝ} (hM : 1 ≤ M) (hK0 : 0 ≤ K)
    (hZ0 : ∀ n ω, 0 < Z n ω) (hW0 : ∀ ω, 0 < W ω)
    (hZM : ∀ n ω, Z n ω ≤ M) (hWM : ∀ ω, W ω ≤ M)
    (hiZ : ∀ n, Integrable (fun ω => (max (-Real.log (Z n ω)) 0)^2) (P n))
    (hiW : Integrable (fun ω => (max (-Real.log (W ω)) 0)^2) Q)
    (hKZ : ∀ n, (∫ ω, (max (-Real.log (Z n ω)) 0)^2 ∂P n) ≤ K)
    (hKW : (∫ ω, (max (-Real.log (W ω)) 0)^2 ∂Q) ≤ K)
    (hfloors : ∀ δ > 0, Tendsto (fun n => ∫ ω, Real.log (Z n ω + δ) ∂P n) atTop
      (𝓝 (∫ ω, Real.log (W ω + δ) ∂Q))) :
    Tendsto (fun n => ∫ ω, Real.log (Z n ω) ∂P n) atTop
      (𝓝 (∫ ω, Real.log (W ω) ∂Q)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ₁, hδ₁, he₁⟩ := cavity_log_floor_uniform P Z hZ hZ0 hZM hM hK0 hiZ hKZ
    (ε / 3) (by positivity)
  obtain ⟨δ₂, hδ₂, he₂⟩ := cavity_log_floor_uniform (fun _ : ℕ => Q)
    (fun _ : ℕ => W) (fun _ => hW) (fun _ => hW0) (fun _ => hWM) hM hK0
    (fun _ => hiW) (fun _ => hKW) (ε / 3) (by positivity)
  let δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hfloors δ hδ) (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h₁ := (he₁ δ ⟨hδ.le, min_le_left _ _⟩ n).2
  have h₂ := (he₂ δ ⟨hδ.le, min_le_right _ _⟩ 0).2
  rw [← cavity_log_floor_mean_difference (P n) (Z n) (hZ n) (hZ0 n) (hZM n) hδ (hiZ n),
    abs_sub_comm] at h₁
  rw [← cavity_log_floor_mean_difference Q W hW hW0 hWM hδ hiW] at h₂
  have h₃ := hN n hn
  rw [Real.dist_eq] at h₃ ⊢
  calc
    _ ≤ |(∫ ω, Real.log (Z n ω) ∂P n) - ∫ ω, Real.log (Z n ω + δ) ∂P n| +
        |(∫ ω, Real.log (Z n ω + δ) ∂P n) - ∫ ω, Real.log (W ω) ∂Q| := abs_sub_le _ _ _
    _ ≤ |(∫ ω, Real.log (Z n ω) ∂P n) - ∫ ω, Real.log (Z n ω + δ) ∂P n| +
        (|(∫ ω, Real.log (Z n ω + δ) ∂P n) - ∫ ω, Real.log (W ω + δ) ∂Q| +
        |(∫ ω, Real.log (W ω + δ) ∂Q) - ∫ ω, Real.log (W ω) ∂Q|) :=
      add_le_add le_rfl (abs_sub_le _ _ _)
    _ < ε := by linarith

end InvariantIsing

end

end OAI
