import OAI.Analysis.LipschitzHilbert.Fourier.BandAverageComparison

namespace OAI

/-! The scalar complex form of the actual-grid variation comparison. -/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace LipschitzHilbert

def scalarVector (z : ℂ) : EuclideanSpace ℂ Unit := WithLp.toLp 2 (fun _ => z)

theorem scalarVector_sub (z w : ℂ) : scalarVector (z - w) = scalarVector z - scalarVector w := by
  ext u
  rfl

theorem norm_scalarVector (z : ℂ) : ‖scalarVector z‖ = ‖z‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [scalarVector, Real.sqrt_sq (norm_nonneg z)]

theorem scalarVector_measurable : Measurable scalarVector := by
  exact (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.mpr (fun _ => measurable_id))

theorem finiteCubicVariation_scalarVector (F : ℕ → ℂ) (N : ℕ) :
    finiteCubicVariation (fun i => scalarVector (F i)) N = finiteCubicVariation F N := by
  unfold finiteCubicVariation
  simp_rw [← scalarVector_sub, norm_scalarVector]

theorem scalarVector_average (g : FiniteLineGrid) (μ : Measure ℝ) (f : ℝ → ℂ)
    (i : ℕ) (x : ℝ) :
    g.complexAverage μ (fun y => scalarVector (f y)) i x =
      scalarVector (g.scalarAverage μ f i x) := by
  ext u
  rfl

theorem scalar_line_variation_comparison (hL : LepingleInput) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (g : FiniteLineGrid) (f : ℝ → ℂ) (P : ℕ → ℝ → ℂ),
      Measurable f → (∀ i, Measurable (P i)) → MemLp f 2 g.lineMeasure → ∀ N : ℕ,
      (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun i => P i x) N) ^ (2 / 3 : ℝ)
        ∂g.lineMeasure) ≤
      2 * (C : ℝ≥0∞) ^ 2 * (∫⁻ x, ‖f x‖ₑ ^ 2 ∂g.lineMeasure) +
        8 * ∑ i : Fin (N + 1), ∫⁻ x, ‖P i.val x - g.scalarAverage g.lineMeasure f i.val x‖ₑ ^ 2
          ∂g.lineMeasure := by
  obtain ⟨C,hC,hbound⟩ := lineGrid_variation_comparison hL
  refine ⟨C,hC,?_⟩
  intro g f P hf hP hf2 N
  have h := hbound g Unit (fun x => scalarVector (f x))
    (fun i x => scalarVector (P i x)) (scalarVector_measurable.comp hf)
    (fun i => scalarVector_measurable.comp (hP i))
    (fun _ => hf2.re) (fun _ => hf2.im) N
  simpa only [finiteCubicVariation_scalarVector, scalarVector_average,
    ← scalarVector_sub, ← ofReal_norm, norm_scalarVector] using h

theorem lintegral_enorm_square (μ : Measure ℝ) (f : ℝ → ℂ) (hf : MemLp f 2 μ) :
    (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) = ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal
    (hf.integrable_norm_pow (by decide : 2 ≠ 0))
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
  simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

end LipschitzHilbert

end

end OAI
