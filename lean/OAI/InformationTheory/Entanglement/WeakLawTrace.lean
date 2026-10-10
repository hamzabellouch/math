import OAI.InformationTheory.Entanglement.WeakStateUnique
import OAI.InformationTheory.Entanglement.HilbertMeasure

namespace OAI

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder MeasureTheory
open ContinuousLinearMap MeasureTheory Filter
namespace SecretKey
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι X : Type*} [MeasurableSpace X]

lemma weak_density_trace_le (b : HilbertBasis ι ℂ H)
    (W : PositiveHilbertMeasure X H b) (μ : Measure X) [IsFiniteMeasure μ]
    (ρ : X→DensityOperator b)
    (hm : ∀ x y : H, Measurable (fun z => inner ℂ x ((ρ z).val.val y)))
    (hd : ∀ s, MeasurableSet s → ∀ x y : H,
      W.coeff x y s=∫ z in s, inner ℂ x ((ρ z).val.val y) ∂μ) :
    W.traceMeasure≤μ := by
  classical
  apply Measure.le_iff.mpr
  intro s hs
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change W.traceMeasure.real s≤μ.real s
  rw [W.trace_value s hs]
  change (∑' i, (inner ℂ (b i) (W.value s (b i))).re)≤μ.real s
  apply (W.positive s hs).2.tsum_le_of_sum_le
  intro t
  have hdiag (i : ι) : Integrable (fun z => densityDiag b (ρ z) i) (μ.restrict s) :=
    (density_coefficient_integrable b μ ρ hm (b i) (b i)).re.integrableOn
  have he (i : ι) : (inner ℂ (b i) (W.value s (b i))).re=
      ∫ z in s, densityDiag b (ρ z) i ∂μ := by
    rw [← W.coeff_value _ _ _ hs,hd s hs]
    exact (integral_re (density_coefficient_integrable b μ ρ hm (b i) (b i)).integrableOn).symm
  simp_rw [he]
  rw [← integral_finsetSum _ (fun i _ => hdiag i)]
  calc
    (∫ z in s, ∑ i∈t, densityDiag b (ρ z) i ∂μ)≤∫ _ in s, (1 : ℝ) ∂μ := by
      apply integral_mono (integrable_finsetSum _ (fun i _ => hdiag i)) (integrable_const _)
      intro z
      rw [← densityDiag_sum b (ρ z)]
      exact (densityDiag_summable b (ρ z)).sum_le_tsum t (fun i _ => densityDiag_nonneg b (ρ z) i)
    _=μ.real s := by simp
lemma weak_density_trace_eq (b : HilbertBasis ι ℂ H)
    (W : PositiveHilbertMeasure X H b) [IsProbabilityMeasure W.traceMeasure]
    (μ : Measure X) [IsProbabilityMeasure μ] (ρ : X→DensityOperator b)
    (hm : ∀ x y : H, Measurable (fun z => inner ℂ x ((ρ z).val.val y)))
    (hd : ∀ s, MeasurableSet s → ∀ x y : H,
      W.coeff x y s=∫ z in s, inner ℂ x ((ρ z).val.val y) ∂μ) :
    W.traceMeasure=μ :=
  Measure.eq_of_le_of_measure_univ_eq (weak_density_trace_le b W μ ρ hm hd) (by simp)

end SecretKey

end

end OAI
