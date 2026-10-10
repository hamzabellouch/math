import OAI.Probability.InvariantIsing.Cavity.CavityWeightedMoments

namespace OAI

/-! Matching replica moments compare two varying models directly.
This applies to the physical system and a refining finite cascade without
postulating a limiting random probability measure for either model. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Polynomial

namespace InvariantIsing

theorem cavity_moving_weighted_moments
    {Ω Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (Ξ n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : (n : ℕ) → Measure (Ξ n)) [∀ n, IsProbabilityMeasure (Q n)]
    (Z A : (n : ℕ) → Ω n → ℝ) (W D : (n : ℕ) → Ξ n → ℝ)
    (hZ : ∀ n, Measurable (Z n)) (hA : ∀ n, Measurable (A n))
    (hW : ∀ n, Measurable (W n)) (hD : ∀ n, Measurable (D n))
    {a b B : ℝ} (hB : 0 ≤ B)
    (hZb : ∀ n ω, Z n ω ∈ Icc a b) (hWb : ∀ n ω, W n ω ∈ Icc a b)
    (hAb : ∀ n ω, |A n ω| ≤ B) (hDb : ∀ n ω, |D n ω| ≤ B)
    (hmom : ∀ k : ℕ, Tendsto (fun n =>
      (∫ ω, A n ω * Z n ω ^ k ∂P n) - ∫ ω, D n ω * W n ω ^ k ∂Q n) atTop (𝓝 0))
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc a b)) :
    Tendsto (fun n => (∫ ω, A n ω * f (Z n ω) ∂P n) -
      ∫ ω, D n ω * f (W n ω) ∂Q n) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := ε / (3 * (B + 1))
  have hη : 0 < η := div_pos hε (by positivity)
  have hηb : B * η < ε / 3 := by
    have he : 3 * (B + 1) * η = ε := mul_div_cancel₀ ε (by positivity)
    nlinarith
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b f hf η hη
  have ht : Tendsto (fun n => (∫ ω, A n ω * p.eval (Z n ω) ∂P n) -
      ∫ ω, D n ω * p.eval (W n ω) ∂Q n) atTop (𝓝 0) := by
    simp_rw [cavity_weighted_polynomial_integral (P _) (Z _) (A _) (hZ _) (hA _)
        (hZb _) (hAb _) p,
      cavity_weighted_polynomial_integral (Q _) (W _) (D _) (hW _) (hD _)
        (hWb _) (hDb _) p, ← Finset.sum_sub_distrib, ← mul_sub]
    simpa only [mul_zero, Finset.sum_const_zero] using
      tendsto_finsetSum p.support (fun k _ => (hmom k).const_mul (p.coeff k))
  have hclose := ht.eventually (Metric.ball_mem_nhds 0 (show 0 < ε / 3 by positivity))
  filter_upwards [hclose] with n hn
  rw [Real.dist_eq, sub_zero] at hn
  rw [Real.dist_eq, sub_zero]
  have h1 := cavity_weighted_approx_error (P n) (Z n) (A n) (hZ n) (hA n)
    (hZb n) (hAb n) (fun x => p.eval x) f p.continuous.continuousOn hf
    (fun x hx => (hp x hx).le)
  have h2 := cavity_weighted_approx_error (Q n) (W n) (D n) (hW n) (hD n)
    (hWb n) (hDb n) (fun x => p.eval x) f p.continuous.continuousOn hf
    (fun x hx => (hp x hx).le)
  have htri := abs_sub_le (∫ ω, A n ω * f (Z n ω) ∂P n)
    (∫ ω, A n ω * p.eval (Z n ω) ∂P n) (∫ ω, D n ω * f (W n ω) ∂Q n)
  have htri' := abs_sub_le (∫ ω, A n ω * p.eval (Z n ω) ∂P n)
    (∫ ω, D n ω * p.eval (W n ω) ∂Q n) (∫ ω, D n ω * f (W n ω) ∂Q n)
  rw [abs_sub_comm] at h1
  linarith

theorem cavity_moving_floored_log
    {Ω Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (Ξ n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : (n : ℕ) → Measure (Ξ n)) [∀ n, IsProbabilityMeasure (Q n)]
    (Z : (n : ℕ) → Ω n → ℝ) (W : (n : ℕ) → Ξ n → ℝ)
    (hZ : ∀ n, Measurable (Z n)) (hW : ∀ n, Measurable (W n))
    {M δ : ℝ} (hδ : 0 < δ)
    (hZb : ∀ n ω, Z n ω ∈ Icc 0 M) (hWb : ∀ n ω, W n ω ∈ Icc 0 M)
    (hmom : ∀ k : ℕ, Tendsto (fun n =>
      (∫ ω, Z n ω ^ k ∂P n) - ∫ ω, W n ω ^ k ∂Q n) atTop (𝓝 0)) :
    Tendsto (fun n => (∫ ω, Real.log (Z n ω + δ) ∂P n) -
      ∫ ω, Real.log (W n ω + δ) ∂Q n) atTop (𝓝 0) := by
  have hf : ContinuousOn (fun z : ℝ => Real.log (z + δ)) (Icc 0 M) :=
    (continuousOn_id.add continuousOn_const).log
      (fun z hz => (add_pos_of_nonneg_of_pos hz.1 hδ).ne')
  simpa only [one_mul] using cavity_moving_weighted_moments P Q Z (fun _ _ => 1)
    W (fun _ _ => 1) hZ (fun _ => measurable_const) hW (fun _ => measurable_const)
    (B := 1) zero_le_one hZb hWb (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    (by simpa only [one_mul] using hmom) _ hf

end InvariantIsing

end

end OAI
