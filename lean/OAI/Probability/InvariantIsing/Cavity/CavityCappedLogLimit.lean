import OAI.Probability.InvariantIsing.Cavity.CavityUnflooredLog
import OAI.Probability.InvariantIsing.Cavity.CavityCappedLog
import OAI.Probability.InvariantIsing.Cavity.CavityRegularizedReweighting

namespace OAI

/-! The logarithmic finite-replica passage with its floor removed.
Fourth moments of the original marks control the negative logarithm. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

lemma cavity_capped_negative_log_mean_bound {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H R : Ω × X → ℝ) (hH : Measurable H)
    (hi : ∀ ω, Integrable (fun x => R (ω, x)^4) (ν ω))
    (hmi : Integrable (fun ω => ∫ x, R (ω, x)^4 ∂ν ω) P)
    {D M T : ℝ} (hD : 0 ≤ D) (hT : 0 ≤ T)
    (hg : ∀ ω x, |H (ω, x)| ≤ D * (1 + R (ω, x)^2))
    (hM : (∫ ω, ∫ x, R (ω, x)^4 ∂ν ω ∂P) ≤ M) :
    Integrable (fun ω => (max (-Real.log
      (∫ x, Real.exp (min (H (ω, x)) T) ∂ν ω)) 0)^2) P ∧
    (∫ ω, (max (-Real.log (∫ x, Real.exp (min (H (ω, x)) T) ∂ν ω)) 0)^2 ∂P) ≤
      2 * D^2 * (1 + M) := by
  have hb ω := cavity_capped_log_negative_sq_of_growth (ν ω) (fun x => H (ω, x))
    (fun x => R (ω, x)) (hH.comp measurable_prodMk_left) (hi ω) hD hT (hg ω)
  have hZ : Measurable (fun ω => ∫ x, Real.exp (min (H (ω, x)) T) ∂ν ω) :=
    measurable_cavityWeightNormalizer ν hν _ ((hH.min measurable_const).exp)
  have he := ((integrable_const 1).add hmi).const_mul (2 * D^2)
  have hN : Integrable (fun ω => (max (-Real.log
      (∫ x, Real.exp (min (H (ω, x)) T) ∂ν ω)) 0)^2) P := by
    apply he.mono' ((hZ.log.neg.max measurable_const).pow_const 2).aestronglyMeasurable
    exact ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hb ω
  refine ⟨hN, ?_⟩
  have hh := integral_mono hN he hb
  simp only [Pi.add_apply, integral_const_mul, integral_add (integrable_const 1) hmi,
    integral_const, probReal_univ, one_smul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl (1 : ℝ)) hM) (by positivity))

theorem cavity_capped_log_limit
    {Ω X : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (X n)]
    {Ω₀ X₀ : Type*} [MeasurableSpace Ω₀] [MeasurableSpace X₀]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : Measure Ω₀) [IsProbabilityMeasure Q]
    (ν : (n : ℕ) → Ω n → Measure (X n)) (hν : ∀ n, Measurable (ν n))
    [∀ n ω, IsProbabilityMeasure (ν n ω)]
    (ρ : Ω₀ → Measure X₀) (hρ : Measurable ρ) [∀ ω, IsProbabilityMeasure (ρ ω)]
    (H R : (n : ℕ) → Ω n × X n → ℝ) (G S : Ω₀ × X₀ → ℝ)
    (hH : ∀ n, Measurable (H n)) (hG : Measurable G)
    (hiR : ∀ n ω, Integrable (fun x => R n (ω, x)^4) (ν n ω))
    (hiS : ∀ ω, Integrable (fun x => S (ω, x)^4) (ρ ω))
    (hmiR : ∀ n, Integrable (fun ω => ∫ x, R n (ω, x)^4 ∂ν n ω) (P n))
    (hmiS : Integrable (fun ω => ∫ x, S (ω, x)^4 ∂ρ ω) Q)
    {D M T : ℝ} (hD : 0 ≤ D) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hgH : ∀ n ω x, |H n (ω, x)| ≤ D * (1 + R n (ω, x)^2))
    (hgG : ∀ ω x, |G (ω, x)| ≤ D * (1 + S (ω, x)^2))
    (hMR : ∀ n, (∫ ω, ∫ x, R n (ω, x)^4 ∂ν n ω ∂P n) ≤ M)
    (hMS : (∫ ω, ∫ x, S (ω, x)^4 ∂ρ ω ∂Q) ≤ M)
    (hmom : ∀ k : ℕ, Tendsto
      (fun n => ∫ ω, ∫ ξ : Fin k → X n,
        (∏ i, Real.exp (min (H n (ω, ξ i)) T)) ∂Measure.pi (fun _ => ν n ω) ∂P n) atTop
      (𝓝 (∫ ω, ∫ ξ : Fin k → X₀,
        (∏ i, Real.exp (min (G (ω, ξ i)) T)) ∂Measure.pi (fun _ => ρ ω) ∂Q))) :
    Tendsto (fun n => ∫ ω, Real.log (∫ x, Real.exp (min (H n (ω, x)) T) ∂ν n ω) ∂P n)
      atTop (𝓝 (∫ ω, Real.log (∫ x, Real.exp (min (G (ω, x)) T) ∂ρ ω) ∂Q)) := by
  let Z n ω := ∫ x, Real.exp (min (H n (ω, x)) T) ∂ν n ω
  let W ω := ∫ x, Real.exp (min (G (ω, x)) T) ∂ρ ω
  have hw n : Measurable (fun p => Real.exp (min (H n p) T)) := ((hH n).min measurable_const).exp
  have hv : Measurable (fun p => Real.exp (min (G p) T)) := (hG.min measurable_const).exp
  have hwb n ω x : Real.exp (min (H n (ω, x)) T) ∈ Set.Icc 0 (Real.exp T) :=
    ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr (min_le_right _ _)⟩
  have hvb ω x : Real.exp (min (G (ω, x)) T) ∈ Set.Icc 0 (Real.exp T) :=
    ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr (min_le_right _ _)⟩
  have hZ n : Measurable (Z n) := measurable_cavityWeightNormalizer (ν n) (hν n) _ (hw n)
  have hW : Measurable W := measurable_cavityWeightNormalizer ρ hρ _ hv
  have hZn n := cavity_capped_negative_log_mean_bound (P n) (ν n) (hν n) (H n) (R n)
    (hH n) (hiR n) (hmiR n) hD hT (hgH n) (hMR n)
  have hWn := cavity_capped_negative_log_mean_bound Q ρ hρ G S hG hiS hmiS hD hT hgG hMS
  apply cavity_unfloored_log_tendsto P Q Z W hZ hW (M := Real.exp T) (K := 2 * D^2 * (1 + M))
    (Real.one_le_exp hT) (by positivity)
  · intro n ω
    apply MeasureTheory.integral_exp_pos
    exact integrable_of_measurable_abs_le ((hw n).comp measurable_prodMk_left)
      (fun x => by rw [abs_of_pos (Real.exp_pos _)]; exact (hwb n ω x).2)
  · intro ω
    apply MeasureTheory.integral_exp_pos
    exact integrable_of_measurable_abs_le (hv.comp measurable_prodMk_left)
      (fun x => by rw [abs_of_pos (Real.exp_pos _)]; exact (hvb ω x).2)
  · exact fun n ω => (cavityWeightNormalizer_mem (ν n ω) _
      ((hw n).comp measurable_prodMk_left) le_rfl (hwb n ω)).2
  · exact fun ω => (cavityWeightNormalizer_mem (ρ ω) _
      (hv.comp measurable_prodMk_left) le_rfl (hvb ω)).2
  · exact fun n => (hZn n).1
  · exact hWn.1
  · exact fun n => (hZn n).2
  · exact hWn.2
  · intro δ hδ
    exact cavity_floored_log_normalizer_tendsto P Q ν hν ρ hρ _ hw _ hv hδ hwb hvb hmom

end InvariantIsing

end

end OAI
