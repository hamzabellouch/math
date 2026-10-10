import OAI.Probability.InvariantIsing.Cavity.CavityCoefficientProbability

namespace OAI

/-! Bounded normalized cavity observables are stable under coefficient
concentration when their cutoff energy has a uniform secant bound. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

theorem cavity_coefficient_values_tendsto {Ω : ℕ → Type*}
    [∀ k, MeasurableSpace (Ω k)] {d n : ℕ}
    (P : (k : ℕ) → Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (A : (k : ℕ) → Ω k → CavityFactorBlocks d n) (hA : ∀ k, Measurable (A k))
    (A₀ : CavityFactorBlocks d n)
    (f g : (k : ℕ) → Ω k → ℝ) (hf : ∀ k, Measurable (f k)) (hg : ∀ k, Measurable (g k))
    {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hfb : ∀ k ω, |f k ω| ≤ M) (hgb : ∀ k ω, |g k ω| ≤ M)
    (hlocal : ∀ k ω s, 0 < s → |f k ω-g k ω| ≤
      K*cavityFactorDeviation (A k ω) A₀/s+M^2*s/2)
    (hprob : ∀ δ > 0, Tendsto (fun k => (P k).real
      {ω | δ < cavityFactorDeviation (A k ω) A₀}) atTop (𝓝 0)) :
    Tendsto (fun k => (∫ ω, f k ω ∂P k) - ∫ ω, g k ω ∂P k) atTop (𝓝 0) := by
  let : OpensMeasurableSpace (CavityFactorBlocks d n) := inferInstanceAs
    (OpensMeasurableSpace ((Fin d → Fin d → ℝ) ×
      ((Fin d → Fin n → ℝ) × (Fin n → Fin n → ℝ))))
  have hmean k (δ s : ℝ) (hδ : 0 ≤ δ) (hs : 0 < s) :
      |(∫ ω, f k ω ∂P k) - ∫ ω, g k ω ∂P k| ≤
        K*δ/s+M^2*s/2+2*M*(P k).real {ω | δ < cavityFactorDeviation (A k ω) A₀} := by
    let bad := {ω : Ω k | δ < cavityFactorDeviation (A k ω) A₀}
    have hbad : MeasurableSet bad := measurableSet_lt measurable_const
      ((continuous_cavityFactorDeviation A₀).measurable.comp (hA k))
    have hfi : Integrable (f k) (P k) := integrable_of_measurable_abs_le (hf k) (hfb k)
    have hgi : Integrable (g k) (P k) := integrable_of_measurable_abs_le (hg k) (hgb k)
    have hb ω : |f k ω-g k ω| ≤ K*δ/s+M^2*s/2+
        2*M*bad.indicator (fun _ => (1 : ℝ)) ω := by
      by_cases hω : ω ∈ bad
      · rw [indicator_of_mem hω, mul_one]
        have ht : |f k ω-g k ω| ≤ 2*M := (abs_sub _ _).trans (by linarith [hfb k ω,hgb k ω])
        exact ht.trans (le_add_of_nonneg_left (by positivity))
      · rw [indicator_of_notMem hω, mul_zero, add_zero]
        have hd : cavityFactorDeviation (A k ω) A₀ ≤ δ := le_of_not_gt hω
        exact (hlocal k ω s hs).trans (add_le_add
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd hK) hs.le) le_rfl)
    have hbi : Integrable (fun ω => K*δ/s+M^2*s/2+
        2*M*bad.indicator (fun _ => (1 : ℝ)) ω) (P k) :=
      (integrable_const _).add (((integrable_const (1 : ℝ)).indicator hbad).const_mul _)
    rw [← integral_sub hfi hgi]
    calc
      _ ≤ ∫ ω, |f k ω-g k ω| ∂P k := abs_integral_le_integral_abs
      _ ≤ ∫ ω, K*δ/s+M^2*s/2+2*M*bad.indicator (fun _ => (1 : ℝ)) ω ∂P k :=
        integral_mono (hfi.sub hgi).abs hbi hb
      _ = _ := by
        rw [integral_add (integrable_const _)
          (((integrable_const (1 : ℝ)).indicator hbad).const_mul _), integral_const_mul,
          integral_indicator hbad, integral_const, integral_const]
        simp only [smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply_univ,
          measure_univ, ENNReal.toReal_one, one_mul, bad]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let s := ε/(4*(M^2+1))
  have hs : 0 < s := by dsimp only [s]; positivity
  have hse : 4*(M^2+1)*s = ε := by
    dsimp only [s]
    field_simp
  let δ := ε*s/(4*(K+1))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδe : 4*(K+1)*δ = ε*s := by
    dsimp only [δ]
    field_simp
  have hsmall : K*δ/s+M^2*s/2 < ε/2 := by
    have hd : K*δ/s < ε/4 := (div_lt_iff₀ hs).mpr (by nlinarith)
    have ht : M^2*s/2 < ε/4 := by nlinarith
    linarith
  have hden : 0 < 4*(2*M+1) := by positivity
  have hevent := (hprob δ hδ).eventually (gt_mem_nhds (show (0 : ℝ) < ε/(4*(2*M+1)) by positivity))
  filter_upwards [hevent] with k hk
  have htail : 2*M*(P k).real {ω | δ < cavityFactorDeviation (A k ω) A₀} < ε/4 := by
    have hh := (lt_div_iff₀ hden).mp hk
    nlinarith [measureReal_nonneg (μ := P k) (s := {ω | δ < cavityFactorDeviation (A k ω) A₀})]
  rw [Real.dist_eq, sub_zero]
  exact (hmean k δ s hδ.le hs).trans_lt (by linarith)

end InvariantIsing

end

end OAI
