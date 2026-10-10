import OAI.Probability.InvariantIsing.Arrays.NSpinConcentration

namespace OAI

/-! The Haar contribution to the enriched pressure variance. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace InvariantIsing

/-- Integrating the Gaussian tail of a deviation gives its second moment.
The proof applies layer cake to the squared deviation, so only the elementary
exponential integral on the positive half-line is needed. -/
lemma integral_sq_sub_le_of_gaussian_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (m C a : ℝ) (hC : 0 ≤ C) (ha : 0 < a)
    (htail : ∀ r : ℝ, 0 < r →
      μ.real {ω | r ≤ |f ω - m|} ≤ C * Real.exp (-a * r ^ 2)) :
    Integrable (fun ω => (f ω - m) ^ 2) μ ∧
      (∫ ω, (f ω - m) ^ 2 ∂μ) ≤ C / a := by
  let g := fun ω => (f ω - m) ^ 2
  have hgm : Measurable g := (hf.sub_const m).pow_const 2
  have hgn : ∀ ω, 0 ≤ g ω := fun ω => sq_nonneg _
  have hk : Integrable (fun t : ℝ => C * Real.exp (-a * t)) (volume.restrict (Ioi 0)) :=
    (integrableOn_exp_mul_Ioi (by linarith : -a < 0) 0).const_mul C
  have hkn : ∀ t : ℝ, 0 ≤ C * Real.exp (-a * t) := fun _ => mul_nonneg hC (Real.exp_pos _).le
  have hki : (∫ t : ℝ in Ioi 0, C * Real.exp (-a * t)) = C / a := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -a < 0) 0]
    simp [div_eq_mul_inv]
  have hlin : (∫⁻ ω, ENNReal.ofReal (g ω) ∂μ) ≤ ENNReal.ofReal (C / a) := by
    calc
      _ = ∫⁻ t : ℝ in Ioi 0, μ {ω | t ≤ g ω} :=
        lintegral_eq_lintegral_meas_le μ (ae_of_all _ hgn) hgm.aemeasurable
      _ ≤ ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (C * Real.exp (-a * t)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have he : {ω | t ≤ g ω} = {ω | Real.sqrt t ≤ |f ω - m|} := by
          ext ω
          simp only [mem_ofPred_eq, g, Real.sqrt_le_left (abs_nonneg _), sq_abs]
        rw [he, ← ofReal_measureReal]
        apply ENNReal.ofReal_le_ofReal
        simpa only [Real.sq_sqrt ht.le] using htail (Real.sqrt t) (Real.sqrt_pos.mpr ht)
      _ = ENNReal.ofReal (C / a) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hk (ae_of_all _ hkn), hki]
  have hgi : Integrable g μ :=
    (lintegral_ofReal_ne_top_iff_integrable hgm.aestronglyMeasurable
      (ae_of_all _ hgn)).mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlin)
  refine ⟨hgi, ?_⟩
  have hI : ENNReal.ofReal (∫ ω, g ω ∂μ) ≤ ENNReal.ofReal (C / a) := by
    rw [ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ hgn)]
    exact hlin
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ C / a)).mp hI

lemma variance_le_of_gaussian_median_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (m C a : ℝ) (hC : 0 ≤ C) (ha : 0 < a)
    (htail : ∀ r : ℝ, 0 < r →
      μ.real {ω | r ≤ |f ω - m|} ≤ C * Real.exp (-a * r ^ 2)) :
    variance f μ ≤ C / a := by
  rw [← variance_sub_const hf.aestronglyMeasurable m]
  exact (variance_le_expectation_sq (hf.sub_const m).aestronglyMeasurable).trans
    (integral_sq_sub_le_of_gaussian_tail μ f hf m C a hC ha htail).2

/-- Haar variance of the actual enriched pressure is at most a universal
constant times the squared spectral bound divided by dimension. -/
theorem haar_enrichedPressure_variance (hpub : HaarConcentrationInput) :
    ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, 3 ≤ N →
    ∀ μ : Measure (SpecialOrthogonal N),
      IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
    ∀ n : ℕ, ∀ b : ℕ → ℝ, ∀ v : ℕ → ℝ≥0, ∀ root : ℝ≥0,
      IsingPerceptron.CascadeExponents n b →
    ∀ eig c : Fin N → ℝ, ∀ K : ℝ, 0 < K → (∀ i, |eig i| ≤ K) →
      variance (fun U : SpecialOrthogonal N =>
        rotatedEnrichedPressure n b v root eig (specialRotation U) c) μ ≤
        C * K ^ 2 / N := by
  obtain ⟨C, a, hC, ha, hp⟩ := haar_enrichedPressure_median_tail hpub
  refine ⟨C / a, by positivity, ?_⟩
  intro N hN μ hμ hμinv n b v root hb eig c K hK heig
  let : IsProbabilityMeasure μ := hμ
  obtain ⟨m, _, _, ht⟩ := hp N hN μ hμ hμinv n b v root hb eig c K hK heig
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbound := variance_le_of_gaussian_median_tail μ
    (fun U : SpecialOrthogonal N => rotatedEnrichedPressure n b v root eig (specialRotation U) c)
    (measurable_rotatedEnrichedPressure n b v root eig c) m C (a * N / K ^ 2) hC.le
    (by positivity) (fun r hr => by
      simpa only [show -a * (N : ℝ) * r ^ 2 / K ^ 2 = -(a * N / K ^ 2) * r ^ 2 by ring]
        using ht r hr)
  refine hbound.trans_eq ?_
  field_simp

end InvariantIsing

end

end OAI
