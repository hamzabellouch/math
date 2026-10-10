import OAI.Probability.InvariantIsing.Cavity.CavityMovingCappedReplica
import OAI.Probability.InvariantIsing.Cavity.CavityMovingLog

namespace OAI

/-! Capped logarithmic comparison with almost-sure prior moments,
as provided by the labeled finite-cascade construction. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem cavity_moving_capped_log_ae
    {Ω X Ξ Y : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (X n)]
    [∀ n, MeasurableSpace (Ξ n)] [∀ n, MeasurableSpace (Y n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : (n : ℕ) → Measure (Ξ n)) [∀ n, IsProbabilityMeasure (Q n)]
    (ν : (n : ℕ) → Ω n → Measure (X n)) (hν : ∀ n, Measurable (ν n))
    [∀ n ω, IsProbabilityMeasure (ν n ω)]
    (ρ : (n : ℕ) → Ξ n → Measure (Y n)) (hρ : ∀ n, Measurable (ρ n))
    [∀ n ω, IsProbabilityMeasure (ρ n ω)]
    (H R : (n : ℕ) → Ω n × X n → ℝ) (G S : (n : ℕ) → Ξ n × Y n → ℝ)
    (hH : ∀ n, Measurable (H n)) (hG : ∀ n, Measurable (G n))
    (hiR : ∀ n, ∀ᵐ ω ∂P n, Integrable (fun x => R n (ω, x)^4) (ν n ω))
    (hiS : ∀ n, ∀ᵐ ω ∂Q n, Integrable (fun x => S n (ω, x)^4) (ρ n ω))
    (hmiR : ∀ n, Integrable (fun ω => ∫ x, R n (ω, x)^4 ∂ν n ω) (P n))
    (hmiS : ∀ n, Integrable (fun ω => ∫ x, S n (ω, x)^4 ∂ρ n ω) (Q n))
    {D M T : ℝ} (hD : 0 ≤ D) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hgH : ∀ n ω x, |H n (ω, x)| ≤ D * (1 + R n (ω, x)^2))
    (hgG : ∀ n ω x, |G n (ω, x)| ≤ D * (1 + S n (ω, x)^2))
    (hMR : ∀ n, (∫ ω, ∫ x, R n (ω, x)^4 ∂ν n ω ∂P n) ≤ M)
    (hMS : ∀ n, (∫ ω, ∫ x, S n (ω, x)^4 ∂ρ n ω ∂Q n) ≤ M)
    (hmom : ∀ k : ℕ, Tendsto (fun n =>
      (∫ ω, ∫ ξ : Fin k → X n,
        (∏ i, Real.exp (min (H n (ω, ξ i)) T)) ∂Measure.pi (fun _ => ν n ω) ∂P n) -
      ∫ ω, ∫ ξ : Fin k → Y n,
        (∏ i, Real.exp (min (G n (ω, ξ i)) T)) ∂Measure.pi (fun _ => ρ n ω) ∂Q n)
        atTop (𝓝 0)) :
    Tendsto (fun n =>
      (∫ ω, Real.log (∫ x, Real.exp (min (H n (ω, x)) T) ∂ν n ω) ∂P n) -
      ∫ ω, Real.log (∫ x, Real.exp (min (G n (ω, x)) T) ∂ρ n ω) ∂Q n)
        atTop (𝓝 0) := by
  let Z n ω := ∫ x, Real.exp (min (H n (ω, x)) T) ∂ν n ω
  let W n ω := ∫ x, Real.exp (min (G n (ω, x)) T) ∂ρ n ω
  have hw n : Measurable (fun p => Real.exp (min (H n p) T)) :=
    ((hH n).min measurable_const).exp
  have hv n : Measurable (fun p => Real.exp (min (G n p) T)) :=
    ((hG n).min measurable_const).exp
  have hwb n ω x : Real.exp (min (H n (ω, x)) T) ∈ Set.Icc 0 (Real.exp T) :=
    ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr (min_le_right _ _)⟩
  have hvb n ω x : Real.exp (min (G n (ω, x)) T) ∈ Set.Icc 0 (Real.exp T) :=
    ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr (min_le_right _ _)⟩
  have hZ n : Measurable (Z n) := measurable_cavityWeightNormalizer (ν n) (hν n) _ (hw n)
  have hW n : Measurable (W n) := measurable_cavityWeightNormalizer (ρ n) (hρ n) _ (hv n)
  have hZn n := cavity_capped_negative_log_mean_bound_ae (P n) (ν n) (hν n) (H n) (R n)
    (hH n) (hiR n) (hmiR n) hD hT (hgH n) (hMR n)
  have hWn n := cavity_capped_negative_log_mean_bound_ae (Q n) (ρ n) (hρ n) (G n) (S n)
    (hG n) (hiS n) (hmiS n) hD hT (hgG n) (hMS n)
  apply cavity_moving_log_of_moments P Q Z W hZ hW
    (M := Real.exp T) (K := 2 * D^2 * (1 + M)) (Real.one_le_exp hT) (by positivity)
  · intro n ω
    apply MeasureTheory.integral_exp_pos
    exact integrable_of_measurable_abs_le ((hw n).comp measurable_prodMk_left)
      (fun x => by rw [abs_of_pos (Real.exp_pos _)]; exact (hwb n ω x).2)
  · intro n ω
    apply MeasureTheory.integral_exp_pos
    exact integrable_of_measurable_abs_le ((hv n).comp measurable_prodMk_left)
      (fun x => by rw [abs_of_pos (Real.exp_pos _)]; exact (hvb n ω x).2)
  · exact fun n ω => (cavityWeightNormalizer_mem (ν n ω) _
      ((hw n).comp measurable_prodMk_left) le_rfl (hwb n ω)).2
  · exact fun n ω => (cavityWeightNormalizer_mem (ρ n ω) _
      ((hv n).comp measurable_prodMk_left) le_rfl (hvb n ω)).2
  · exact fun n => (hZn n).1
  · exact fun n => (hWn n).1
  · exact fun n => (hZn n).2
  · exact fun n => (hWn n).2
  · intro k
    have hp n ω : Z n ω ^ k = ∫ ξ : Fin k → X n,
        (∏ i, Real.exp (min (H n (ω, ξ i)) T)) ∂Measure.pi (fun _ => ν n ω) := by
      simpa only [Z, Fintype.card_fin] using
        (integral_fintype_prod_eq_pow (ι := Fin k) (μ := ν n ω)
          (fun x => Real.exp (min (H n (ω, x)) T))).symm
    have hq n ω : W n ω ^ k = ∫ ξ : Fin k → Y n,
        (∏ i, Real.exp (min (G n (ω, ξ i)) T)) ∂Measure.pi (fun _ => ρ n ω) := by
      simpa only [W, Fintype.card_fin] using
        (integral_fintype_prod_eq_pow (ι := Fin k) (μ := ρ n ω)
          (fun x => Real.exp (min (G n (ω, x)) T))).symm
    simpa only [hp, hq] using hmom k

end InvariantIsing

end

end OAI
