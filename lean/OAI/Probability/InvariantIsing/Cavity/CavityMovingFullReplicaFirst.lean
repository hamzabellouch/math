import OAI.Probability.InvariantIsing.Cavity.CavityReplicaCapFirstMoment

namespace OAI

/-! Removing the energy cap in moving finite-system / cascade replica
comparisons, using uniform first absolute moments of the actual tilted energies. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

theorem cavity_moving_full_replica_first
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
    (hH : ∀ n, Measurable (H n)) (hG : ∀ n, Measurable (G n)) {r : ℕ}
    (F : (n : ℕ) → Ω n × (Fin r → X n) → ℝ) (hF : ∀ n, Measurable (F n))
    (V : (n : ℕ) → Ξ n × (Fin r → Y n) → ℝ) (hV : ∀ n, Measurable (V n))
    {B : ℝ} (hB : 0 ≤ B)
    (hFb : ∀ n ω σ, |F n (ω,σ)| ≤ B) (hVb : ∀ n ω σ, |V n (ω,σ)| ≤ B)
    (heH : ∀ n, ∀ᵐ ω ∂P n, Integrable (fun x => Real.exp (H n (ω,x))) (ν n ω))
    (heG : ∀ n, ∀ᵐ ω ∂Q n, Integrable (fun x => Real.exp (G n (ω,x))) (ρ n ω))
    (hiH : ∀ n, ∀ᵐ ω ∂P n, Integrable (fun x => |H n (ω,x)|)
      ((ν n ω).tilted (fun x => H n (ω,x))))
    (hiG : ∀ n, ∀ᵐ ω ∂Q n, Integrable (fun x => |G n (ω,x)|)
      ((ρ n ω).tilted (fun x => G n (ω,x))))
    (hmH : ∀ n, Integrable (fun ω => ∫ x, |H n (ω,x)|
      ∂(ν n ω).tilted (fun x => H n (ω,x))) (P n))
    (hmG : ∀ n, Integrable (fun ω => ∫ x, |G n (ω,x)|
      ∂(ρ n ω).tilted (fun x => G n (ω,x))) (Q n))
    {K : ℝ} (hK : 0 ≤ K)
    (hKH : ∀ n, (∫ ω, ∫ x, |H n (ω,x)| ∂(ν n ω).tilted (fun x => H n (ω,x)) ∂P n) ≤ K)
    (hKG : ∀ n, (∫ ω, ∫ x, |G n (ω,x)| ∂(ρ n ω).tilted (fun x => G n (ω,x)) ∂Q n) ≤ K)
    (hcap : ∀ T > 0, Tendsto (fun n =>
      (∫ ω, cavityWeightedReplicaMean (ν n ω) (fun x => Real.exp (min (H n (ω,x)) T))
        (fun σ => F n (ω,σ)) ∂P n) -
      ∫ ω, cavityWeightedReplicaMean (ρ n ω) (fun x => Real.exp (min (G n (ω,x)) T))
        (fun σ => V n (ω,σ)) ∂Q n) atTop (𝓝 0)) :
    Tendsto (fun n =>
      (∫ ω, cavityWeightedReplicaMean (ν n ω) (fun x => Real.exp (H n (ω,x)))
        (fun σ => F n (ω,σ)) ∂P n) -
      ∫ ω, cavityWeightedReplicaMean (ρ n ω) (fun x => Real.exp (G n (ω,x)))
        (fun σ => V n (ω,σ)) ∂Q n) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let A := 2 * B * r * K
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  let T := 1 + 6 * A / ε
  have hT : 0 < T := by dsimp only [T]; positivity
  have hAT : A / T < ε / 6 := by
    apply (div_lt_iff₀ hT).mpr
    have he : T * ε = ε + 6 * A := by dsimp only [T]; field_simp
    nlinarith
  have hclose := (hcap T hT).eventually
    (Metric.ball_mem_nhds 0 (show 0 < ε / 3 by positivity))
  filter_upwards [hclose] with n hn
  rw [Real.dist_eq, sub_zero] at hn ⊢
  have h₁ := cavity_replica_cap_expectation_error_first (P n) (ν n) (hν n) (H n) (hH n)
    (F n) (hF n) (heH n) (hiH n) (hmH n) hB hT (hFb n) (hKH n)
  have h₂ := cavity_replica_cap_expectation_error_first (Q n) (ρ n) (hρ n) (G n) (hG n)
    (V n) (hV n) (heG n) (hiG n) (hmG n) hB hT (hVb n) (hKG n)
  rw [abs_sub_comm] at h₁
  change |_ - _| ≤ A / T at h₁ h₂
  have htri := abs_sub_le
    (∫ ω, cavityWeightedReplicaMean (ν n ω) (fun x => Real.exp (H n (ω,x)))
      (fun σ => F n (ω,σ)) ∂P n)
    (∫ ω, cavityWeightedReplicaMean (ν n ω) (fun x => Real.exp (min (H n (ω,x)) T))
      (fun σ => F n (ω,σ)) ∂P n)
    (∫ ω, cavityWeightedReplicaMean (ρ n ω) (fun x => Real.exp (G n (ω,x)))
      (fun σ => V n (ω,σ)) ∂Q n)
  have htri' := abs_sub_le
    (∫ ω, cavityWeightedReplicaMean (ν n ω) (fun x => Real.exp (min (H n (ω,x)) T))
      (fun σ => F n (ω,σ)) ∂P n)
    (∫ ω, cavityWeightedReplicaMean (ρ n ω) (fun x => Real.exp (min (G n (ω,x)) T))
      (fun σ => V n (ω,σ)) ∂Q n)
    (∫ ω, cavityWeightedReplicaMean (ρ n ω) (fun x => Real.exp (G n (ω,x)))
      (fun σ => V n (ω,σ)) ∂Q n)
  linarith

end InvariantIsing

end

end OAI
