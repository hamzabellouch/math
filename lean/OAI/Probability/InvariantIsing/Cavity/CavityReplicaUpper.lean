import OAI.Probability.InvariantIsing.Cavity.CavityDisorderMean

namespace OAI

/-! One-sided bounded test estimates, valid also at a zero normalizer. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_referenceReplicaMean_le_const {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SigmaFinite ν] (H : X → ℝ) {r : ℕ}
    (F : (Fin r → X) → ℝ) (hm : Measurable F) {B c : ℝ}
    (hb : ∀ σ, |F σ| ≤ B) (hc : 0 ≤ c) (hF : ∀ σ, F σ ≤ c) :
    referenceReplicaMean ν H F ≤ c := by
  rw [referenceReplicaMean_eq_ratio]
  by_cases hi : Integrable (fun σ : Fin r → X => Real.exp (∑ i, H (σ i)))
      (Measure.pi (fun _ => ν))
  · have hprod := hi.mul_bdd hm.aestronglyMeasurable
      (ae_of_all _ fun σ => by simpa only [Real.norm_eq_abs] using hb σ)
    have hnum : (∫ σ : Fin r → X, Real.exp (∑ i, H (σ i)) * F σ ∂Measure.pi (fun _ : Fin r => ν)) ≤
        c * ∫ σ : Fin r → X, Real.exp (∑ i, H (σ i)) ∂Measure.pi (fun _ : Fin r => ν) := by
      rw [← integral_const_mul]
      apply integral_mono hprod (hi.const_mul c)
      intro σ
      exact (mul_le_mul_of_nonneg_left (hF σ) (Real.exp_pos _).le).trans_eq (mul_comm _ _)
    have hz : 0 ≤ ∫ σ : Fin r → X, Real.exp (∑ i, H (σ i)) ∂Measure.pi (fun _ => ν) :=
      integral_nonneg fun _ => (Real.exp_pos _).le
    rcases hz.eq_or_lt with hz | hz
    · rw [← hz, div_zero]
      exact hc
    · exact (div_le_iff₀ hz).mpr hnum
  · rw [integral_undef hi, div_zero]
    exact hc

lemma cavity_nested_disorder_upper {Ω Ω' X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure Ω') [IsProbabilityMeasure P]
    (ν : Measure X) [SigmaFinite ν] (H : Ω → Ω' → X → ℝ) {r : ℕ}
    (F : Ω → (Fin r → X) → ℝ) (hmF : ∀ ω, Measurable (F ω))
    (hmeas : Measurable (fun z : Ω × Ω' => referenceReplicaMean ν (H z.1 z.2) (F z.1)))
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ ω σ, |F ω σ| ≤ B)
    (c : Ω → ℝ) (hc : Integrable c μ) (hc0 : ∀ ω, 0 ≤ c ω)
    (hFc : ∀ ω σ, F ω σ ≤ c ω) :
    (∫ ω, ∫ g, referenceReplicaMean ν (H ω g) (F ω) ∂P ∂μ) ≤ ∫ ω, c ω ∂μ := by
  have hib (ω : Ω) : Integrable (fun g => referenceReplicaMean ν (H ω g) (F ω)) P :=
    integrable_of_measurable_abs_le (hmeas.comp measurable_prodMk_left)
      (fun g => referenceReplicaMean_abs_le ν (H ω g) (F ω) (hmF ω) hB (hF ω))
  have hi : Integrable (fun ω => ∫ g, referenceReplicaMean ν (H ω g) (F ω) ∂P) μ :=
    integrable_of_measurable_abs_le hmeas.stronglyMeasurable.integral_prod_right'.measurable
      (fun ω => abs_integral_le_const_of_bound (hmeas.comp measurable_prodMk_left)
        (fun g => referenceReplicaMean_abs_le ν (H ω g) (F ω) (hmF ω) hB (hF ω)))
  apply integral_mono hi hc
  intro ω
  calc
    _ ≤ ∫ _ : Ω', c ω ∂P := integral_mono (hib ω) (integrable_const _)
      (fun g => cavity_referenceReplicaMean_le_const ν (H ω g) (F ω) (hmF ω)
        (hF ω) (hc0 ω) (hFc ω))
    _ = c ω := by simp

end InvariantIsing

end

end OAI
