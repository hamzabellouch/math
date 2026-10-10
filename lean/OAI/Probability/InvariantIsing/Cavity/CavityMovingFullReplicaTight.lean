import OAI.Probability.InvariantIsing.Cavity.CavityCapTailAverage

namespace OAI

/-! Full replica comparison from capped comparison and tightness of
the actual full Gibbs radial coordinates. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

theorem cavity_moving_full_replica_tight
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
    (hH : ∀ n, Measurable (H n)) (hR : ∀ n, Measurable (R n))
    (hG : ∀ n, Measurable (G n)) (hS : ∀ n, Measurable (S n)) {r : ℕ}
    (F : (n : ℕ) → Ω n × (Fin r → X n) → ℝ) (hF : ∀ n, Measurable (F n))
    (V : (n : ℕ) → Ξ n × (Fin r → Y n) → ℝ) (hV : ∀ n, Measurable (V n))
    {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hFb : ∀ n ω σ, |F n (ω,σ)| ≤ B) (hVb : ∀ n ω σ, |V n (ω,σ)| ≤ B)
    (hgH : ∀ n ω x, |H n (ω,x)| ≤ D * (1 + (R n (ω,x))^2))
    (hgG : ∀ n ω x, |G n (ω,x)| ≤ D * (1 + (S n (ω,x))^2))
    (heH : ∀ n, ∀ᵐ ω ∂P n, Integrable (fun x => Real.exp (H n (ω,x))) (ν n ω))
    (heG : ∀ n, ∀ᵐ ω ∂Q n, Integrable (fun x => Real.exp (G n (ω,x))) (ρ n ω))
    (htight : ∀ ε > 0, ∃ A > 0, ∀ᶠ n in atTop,
      (∫ ω, ((ν n ω).tilted (fun x => H n (ω,x))).real {x | A < |R n (ω,x)|} ∂P n) +
      (∫ ω, ((ρ n ω).tilted (fun x => G n (ω,x))).real {x | A < |S n (ω,x)|} ∂Q n) < ε)
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
  let C := 2 * B * r
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hCp : 0 < C + 1 := by linarith
  obtain ⟨A, hA, ht⟩ := htight (ε / (3 * (C + 1))) (by positivity)
  let T := 1 + D * (1 + A^2)
  have hT : 0 < T := by dsimp only [T]; positivity
  have hloc {z h : ℝ} (hz : ¬ A < |z|) (hh : |h| ≤ D * (1 + z^2)) : h ≤ T := by
    have hz' : z^2 ≤ A^2 := by
      have hp := pow_le_pow_left₀ (abs_nonneg z) (le_of_not_gt hz) 2
      simpa only [sq_abs] using hp
    have hh' := (le_abs_self h).trans hh
    have := mul_le_mul_of_nonneg_left (add_le_add_left hz' 1) hD
    dsimp only [T]
    linarith
  have hc := (hcap T hT).eventually (Metric.ball_mem_nhds 0 (show 0 < ε/3 by positivity))
  filter_upwards [ht, hc] with n htn hcn
  rw [Real.dist_eq, sub_zero] at hcn ⊢
  have h₁ := cavity_replica_cap_tail_expectation (P n) (ν n) (hν n) (H n) (hH n)
    (F n) (hF n) (heH n) T (fun ω => {x | A < |R n (ω,x)|})
    (measurableSet_lt measurable_const (hR n).abs)
    (fun ω x hx => hloc hx (hgH n ω x)) hB (hFb n)
  have h₂ := cavity_replica_cap_tail_expectation (Q n) (ρ n) (hρ n) (G n) (hG n)
    (V n) (hV n) (heG n) T (fun ω => {x | A < |S n (ω,x)|})
    (measurableSet_lt measurable_const (hS n).abs)
    (fun ω x hx => hloc hx (hgG n ω x)) hB (hVb n)
  let t₁ := ∫ ω, ((ν n ω).tilted (fun x => H n (ω,x))).real {x | A < |R n (ω,x)|} ∂P n
  let t₂ := ∫ ω, ((ρ n ω).tilted (fun x => G n (ω,x))).real {x | A < |S n (ω,x)|} ∂Q n
  have ht₁ : 0 ≤ t₁ := integral_nonneg (fun _ => ENNReal.toReal_nonneg)
  have ht₂ : 0 ≤ t₂ := integral_nonneg (fun _ => ENNReal.toReal_nonneg)
  have hsmall : C * (t₁ + t₂) < ε / 3 := by
    have hs := (lt_div_iff₀ (show 0 < 3 * (C + 1) by positivity)).mp htn
    change (t₁ + t₂) * (3 * (C + 1)) < ε at hs
    nlinarith
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
  rw [abs_sub_comm] at h₁
  change |_ - _| ≤ C * t₁ at h₁
  change |_ - _| ≤ C * t₂ at h₂
  nlinarith

end InvariantIsing

end

end OAI
