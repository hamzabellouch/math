import OAI.Probability.InvariantIsing.Cavity.CavityMovingCappedLog
import OAI.Probability.InvariantIsing.Cavity.CavityLogCapIntegrable

namespace OAI

/-! Removal of the energy cap after matching the finite-system and
finite-cascade logarithmic normalizers. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

theorem cavity_moving_full_log
    {Ω X Ξ Y : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (X n)]
    [∀ n, MeasurableSpace (Ξ n)] [∀ n, MeasurableSpace (Y n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : (n : ℕ) → Measure (Ξ n)) [∀ n, IsProbabilityMeasure (Q n)]
    (ν : (n : ℕ) → Ω n → Measure (X n)) (hν : ∀ n, Measurable (ν n))
    [∀ n ω, IsProbabilityMeasure (ν n ω)]
    (ρ : (n : ℕ) → Ξ n → Measure (Y n)) (hρ : ∀ n, Measurable (ρ n))
    [∀ n ω, IsProbabilityMeasure (ρ n ω)]
    (H : (n : ℕ) → Ω n × X n → ℝ) (G : (n : ℕ) → Ξ n × Y n → ℝ)
    (hH : ∀ n, Measurable (H n)) (hG : ∀ n, Measurable (G n))
    (heH : ∀ n, ∀ᵐ ω ∂P n, Integrable (fun x => Real.exp (H n (ω,x))) (ν n ω))
    (heG : ∀ n, ∀ᵐ ω ∂Q n, Integrable (fun x => Real.exp (G n (ω,x))) (ρ n ω))
    (hiH : ∀ n, ∀ᵐ ω ∂P n, Integrable (fun x => H n (ω,x)^2)
      ((ν n ω).tilted (fun x => H n (ω,x))))
    (hiG : ∀ n, ∀ᵐ ω ∂Q n, Integrable (fun x => G n (ω,x)^2)
      ((ρ n ω).tilted (fun x => G n (ω,x))))
    (hmH : ∀ n, Integrable (fun ω => ∫ x, H n (ω,x)^2
      ∂(ν n ω).tilted (fun x => H n (ω,x))) (P n))
    (hmG : ∀ n, Integrable (fun ω => ∫ x, G n (ω,x)^2
      ∂(ρ n ω).tilted (fun x => G n (ω,x))) (Q n))
    {K : ℝ} (hK : 0 ≤ K)
    (hKH : ∀ n, (∫ ω, ∫ x, H n (ω,x)^2 ∂(ν n ω).tilted (fun x => H n (ω,x)) ∂P n) ≤ K)
    (hKG : ∀ n, (∫ ω, ∫ x, G n (ω,x)^2 ∂(ρ n ω).tilted (fun x => G n (ω,x)) ∂Q n) ≤ K)
    (hcH : ∀ n T, 0 < T → Integrable
      (fun ω => Real.log (∫ x, Real.exp (min (H n (ω,x)) T) ∂ν n ω)) (P n))
    (hcG : ∀ n T, 0 < T → Integrable
      (fun ω => Real.log (∫ x, Real.exp (min (G n (ω,x)) T) ∂ρ n ω)) (Q n))
    (hcap : ∀ T > 0, Tendsto (fun n =>
      (∫ ω, Real.log (∫ x, Real.exp (min (H n (ω,x)) T) ∂ν n ω) ∂P n) -
      ∫ ω, Real.log (∫ x, Real.exp (min (G n (ω,x)) T) ∂ρ n ω) ∂Q n) atTop (𝓝 0)) :
    Tendsto (fun n => (∫ ω, Real.log (∫ x, Real.exp (H n (ω,x)) ∂ν n ω) ∂P n) -
      ∫ ω, Real.log (∫ x, Real.exp (G n (ω,x)) ∂ρ n ω) ∂Q n) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let T := 1 + 6 * K / ε
  have hT : 0 < T := by dsimp only [T]; positivity
  have hKT : K / T < ε / 6 := by
    apply (div_lt_iff₀ hT).mpr
    have he : T * ε = ε + 6 * K := by dsimp only [T]; field_simp
    nlinarith
  have hclose := (hcap T hT).eventually
    (Metric.ball_mem_nhds 0 (show 0 < ε / 3 by positivity))
  filter_upwards [hclose] with n hn
  rw [Real.dist_eq, sub_zero] at hn ⊢
  have h₁ := cavity_log_cap_expectation_error (P n) (ν n) (hν n) (H n) (hH n)
    (heH n) (hiH n) (hmH n) (hKH n) hT (hcH n T hT)
  have h₂ := cavity_log_cap_expectation_error (Q n) (ρ n) (hρ n) (G n) (hG n)
    (heG n) (hiG n) (hmG n) (hKG n) hT (hcG n T hT)
  have htri := abs_sub_le
    (∫ ω, Real.log (∫ x, Real.exp (H n (ω,x)) ∂ν n ω) ∂P n)
    (∫ ω, Real.log (∫ x, Real.exp (min (H n (ω,x)) T) ∂ν n ω) ∂P n)
    (∫ ω, Real.log (∫ x, Real.exp (G n (ω,x)) ∂ρ n ω) ∂Q n)
  have htri' := abs_sub_le
    (∫ ω, Real.log (∫ x, Real.exp (min (H n (ω,x)) T) ∂ν n ω) ∂P n)
    (∫ ω, Real.log (∫ x, Real.exp (min (G n (ω,x)) T) ∂ρ n ω) ∂Q n)
    (∫ ω, Real.log (∫ x, Real.exp (G n (ω,x)) ∂ρ n ω) ∂Q n)
  rw [abs_sub_comm] at h₂
  linarith

end InvariantIsing

end

end OAI
