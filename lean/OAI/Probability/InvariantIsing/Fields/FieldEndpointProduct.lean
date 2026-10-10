import OAI.Probability.InvariantIsing.Fields.FieldCanonicalEndpoint
import OAI.Probability.InvariantIsing.Fields.FieldEndpointSampling
import Mathlib.MeasureTheory.Integral.Pi

namespace OAI

/-! The full endpoint kernel preserves independence across the sites. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators NNReal

namespace InvariantIsing

lemma kernel_comp_real {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (κ : Kernel X Y) [IsMarkovKernel κ] (μ : Measure X) [IsProbabilityMeasure μ]
    (s : Set Y) (hs : MeasurableSet s) :
    (κ ∘ₘ μ).real s = ∫ x, (κ x).real s ∂μ := by
  have hi : Integrable (s.indicator (fun _ : Y => (1 : ℝ))) (κ ∘ₘ μ) :=
    (integrable_const 1).indicator hs
  have he := integral_indicator_one (μ := κ ∘ₘ μ) hs
  rw [Measure.comp_eq_comp_const_apply] at hi
  have hc := Kernel.integral_comp hi
  simp only [Kernel.const_apply] at hc
  rw [← Measure.comp_eq_comp_const_apply] at hc
  have ht (x : X) : (∫ y, s.indicator (fun _ : Y => (1 : ℝ)) y ∂κ x) =
      (κ x).real s := integral_indicator_one (μ := κ x) hs
  simp_rw [ht] at hc
  exact he.symm.trans hc

lemma product_kernel_comp {N : ℕ} (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    (K : Kernel (Fin N → ℝ) (Fin N → ℝ)) [IsMarkovKernel K]
    (hK : ∀ z, K z = Measure.pi (fun i => κ (z i)))
    (ν : Fin N → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] :
    K ∘ₘ Measure.pi ν = Measure.pi (fun i => κ ∘ₘ ν i) := by
  apply (Measure.pi_eq (μ := fun i => κ ∘ₘ ν i) ?_).symm
  intro s hs
  suffices hreal : ((K ∘ₘ Measure.pi ν) (univ.pi s)).toReal =
      (∏ i, (κ ∘ₘ ν i) (s i)).toReal by
    have he := congrArg ENNReal.ofReal hreal
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _),
      ENNReal.ofReal_toReal (ENNReal.prod_ne_top (fun i _ => measure_ne_top _ _))] at he
    exact he
  rw [← measureReal_def, kernel_comp_real K (Measure.pi ν) _ (MeasurableSet.univ_pi hs)]
  have he (z : Fin N → ℝ) : (K z).real (univ.pi s) =
      ∏ i, (κ (z i)).real (s i) := by
    rw [hK, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
    rfl
  simp_rw [he]
  change (∫ z : Fin N → ℝ, ∏ i,
    (fun y : ℝ => (κ y).real (s i)) (z i) ∂Measure.pi ν) = _
  rw [integral_fintype_prod_eq_prod (fun i y => (κ y).real (s i)), ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact (kernel_comp_real κ (ν i) (s i) (hs i)).symm

theorem fieldVectorTailEndpointKernel_product (N : ℕ) (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (z : Fin N → ℝ) :
    fieldVectorTailEndpointKernel N L hL z =
      Measure.pi (fun i => fieldTailEndpointKernel L hL (z i)) := by
  induction L generalizing z with
  | nil =>
    change Measure.dirac z = Measure.pi (fun i => Measure.dirac (z i))
    apply (Measure.pi_eq (μ := fun i => Measure.dirac (z i)) ?_).symm
    intro s hs
    simp only [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs),
      Measure.dirac_apply' _ (hs _)]
    have hz : (z ∈ univ.pi s) ↔ (∀ i ∈ (Finset.univ : Finset (Fin N)), z i ∈ s i) := by
      change (∀ i ∈ (Set.univ : Set (Fin N)), z i ∈ s i) ↔ _
      simp only [Set.mem_univ, Finset.mem_univ, true_implies]
    simp only [Set.indicator, Pi.one_apply, Finset.prod_boole]
    by_cases h : z ∈ univ.pi s
    · simp only [ite_eq_left h, ite_eq_left (hz.mp h)]
    · have hn : ¬ ∀ i ∈ (Finset.univ : Finset (Fin N)), z i ∈ s i := fun hh => h (hz.mpr hh)
      simp only [ite_eq_right h, ite_eq_right hn]
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hreg := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    change (fieldVectorTailEndpointKernel N L ht ∘ₖ
      fieldVectorTransitionKernel N av.1 av.2 _ hreg.1) z = _
    rw [Kernel.comp_apply]
    change fieldVectorTailEndpointKernel N L ht ∘ₘ
      Measure.pi (fun i => fieldTransitionKernel av.1 av.2 _ hreg.1 (z i)) = _
    rw [product_kernel_comp (fieldTailEndpointKernel L ht)
      (fieldVectorTailEndpointKernel N L ht) (ih ht)]
    rfl

end InvariantIsing

end

end OAI
