import OAI.Probability.InvariantIsing.Haar.HaarHeatMixing

namespace OAI

/-! Continuous tests of the polynomial heat flow and their Haar limits. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Filter Set
open scoped Topology
namespace InvariantIsing

lemma haarPolynomialHeat_test_bound {N d : ℕ} (p : haarPolynomialSpace N d)
    (F : ℝ → ℝ) (hF : Continuous F) :
    ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ U : SpecialOrthogonal N,
      ‖F (haarPolynomialValue
        ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) U)‖ ≤ B := by
  obtain ⟨P,hP⟩ := haarPolynomialValue_bound (p : MatrixPolynomial N)
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨B,?_⟩
  intro t ht U
  apply hB
  exact haarPolynomialHeat_bounds p (-P) P
    (fun V => (abs_le.mp (hP V)).1) (fun V => (abs_le.mp (hP V)).2) ht U

theorem haarPolynomialHeat_test_tendsto_mean {N d : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (p : haarPolynomialSpace N d) (F : ℝ → ℝ) (hF : Continuous F) :
    Tendsto (fun t : ℝ => ∫ U, F (haarPolynomialValue
      ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) U) ∂μ)
      atTop (𝓝 (F (∫ U, haarPolynomialValue (p : MatrixPolynomial N) U ∂μ))) := by
  obtain ⟨B,hB⟩ := haarPolynomialHeat_test_bound p F hF
  have h := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atTop)
    (F := fun t U => F (haarPolynomialValue
      ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) U))
    (f := fun _ => F (∫ U, haarPolynomialValue (p : MatrixPolynomial N) U ∂μ)) (fun _ => B)
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at h
  apply h
  · exact Eventually.of_forall fun t =>
      (hF.comp (continuous_haarPolynomialValue _)).measurable.aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact ae_of_all μ (hB t ht)
  · exact integrable_const _
  · exact ae_of_all μ fun U => hF.continuousAt.tendsto.comp (haarPolynomialHeat_tendsto_mean hN μ p U)

theorem continuousOn_haarPolynomialHeat_test_integral {N d : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsFiniteMeasure μ]
    (p : haarPolynomialSpace N d) (F : ℝ → ℝ) (hF : Continuous F) :
    ContinuousOn (fun t : ℝ => ∫ U, F (haarPolynomialValue
      ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) U) ∂μ) (Ici 0) := by
  obtain ⟨B,hB⟩ := haarPolynomialHeat_test_bound p F hF
  intro t _
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => B)
  · exact Eventually.of_forall fun s =>
      (hF.comp (continuous_haarPolynomialValue _)).measurable.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact ae_of_all μ (hB s hs)
  · exact integrable_const _
  · exact ae_of_all μ fun U => ((hF.comp
      ((continuous_haarPolynomialHeat_value p).comp (continuous_id.prodMk continuous_const))).continuousAt).tendsto.mono_left
        nhdsWithin_le_nhds

end InvariantIsing

end

end OAI
