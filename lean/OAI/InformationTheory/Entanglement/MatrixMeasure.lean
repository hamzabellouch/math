import OAI.InformationTheory.Entanglement.DensityGap

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder ENNReal MeasureTheory Matrix.Norms.L2Operator
open Matrix MeasureTheory
namespace SecretKey
open ChannelCompletion
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma complex_setIntegral_rnDeriv (c : ComplexMeasure Ω) [SigmaFinite μ]
    (hc : c ≪ᵥ μ.toENNRealVectorMeasure) {s : Set Ω} (hs : MeasurableSet s) :
    (∫ x in s, c.rnDeriv μ x ∂μ)=c s := by
  have h := (ComplexMeasure.absolutelyContinuous_ennreal_iff c _).mp hc
  have hr := congrArg (fun v : SignedMeasure Ω => v s)
    (SignedMeasure.withDensityᵥ_rnDeriv_eq c.re μ h.1)
  have hi := congrArg (fun v : SignedMeasure Ω => v s)
    (SignedMeasure.withDensityᵥ_rnDeriv_eq c.im μ h.2)
  rw [withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv _ _) hs] at hr hi
  apply Complex.ext
  · exact (integral_re (c.integrable_rnDeriv μ).integrableOn).symm.trans hr
  · exact (integral_im (c.integrable_rnDeriv μ).integrableOn).symm.trans hi

lemma measurable_complex_rnDeriv (c : ComplexMeasure Ω) : Measurable (c.rnDeriv μ) := by
  have he : c.rnDeriv μ = fun x => ((c.re.rnDeriv μ x : ℝ) : ℂ) +
      ((c.im.rnDeriv μ x : ℝ) : ℂ)*Complex.I := by funext x; exact (Complex.re_add_im (c.rnDeriv μ x)).symm
  rw [he]
  exact (SignedMeasure.measurable_rnDeriv c.re μ).complex_ofReal.add
    ((SignedMeasure.measurable_rnDeriv c.im μ).complex_ofReal.mul_const _)

variable {n : Type} [Fintype n]

structure PositiveMatrixMeasure (Ω : Type*) [MeasurableSpace Ω] (n : Type) [Fintype n] where
  entry : Matrix n n (ComplexMeasure Ω)
  positive : ∀ s, MeasurableSet s → Matrix.PosSemidef (fun i j => entry i j s)
namespace PositiveMatrixMeasure
variable (W : PositiveMatrixMeasure Ω n)
def value (s : Set Ω) : Mat n := fun i j => W.entry i j s
def density (μ : Measure Ω) (x : Ω) : Mat n := fun i j => (W.entry i j).rnDeriv μ x
lemma density_integrable (i j : n) : Integrable (fun x => W.density μ x i j) μ :=
  (W.entry i j).integrable_rnDeriv μ
lemma density_measurable : Measurable (W.density μ) := by
  change @Measurable Ω (n → n → ℂ) _ (borel _) _
  rw [← @BorelSpace.measurable_eq (n → n → ℂ) _ MeasurableSpace.pi _]
  exact Measurable.of_eval fun row => Measurable.of_eval fun column =>
    measurable_complex_rnDeriv (W.entry row column)
lemma entry_absolutelyContinuous
    (hdom : ∀ s, MeasurableSet s → μ s=0 → (Matrix.trace (W.value s)).re=0) (i j : n) :
    W.entry i j ≪ᵥ μ.toENNRealVectorMeasure := by
  intro s hs
  by_cases hsm : MeasurableSet s
  · have hz : μ s=0 := by simpa only [Measure.toENNRealVectorMeasure_apply,ite_eq_left hsm] using hs
    have hp := W.positive s hsm
    have ht : Matrix.trace (W.value s)=0 := by
      apply Complex.ext
      · exact hdom s hsm hz
      · exact (Complex.nonneg_iff.mp hp.trace_nonneg).2.symm
    have hm : W.value s=0 := hp.trace_eq_zero_iff.mp ht
    exact congrArg (fun M : Mat n => M i j) hm
  · exact (W.entry i j).not_measurable hsm
lemma density_setIntegral [SigmaFinite μ]
    (hdom : ∀ s, MeasurableSet s → μ s=0 → (Matrix.trace (W.value s)).re=0)
    {s : Set Ω} (hs : MeasurableSet s) (i j : n) :
    (∫ x in s, W.density μ x i j ∂μ)=W.value s i j :=
  complex_setIntegral_rnDeriv _ (W.entry_absolutelyContinuous hdom i j) hs
end PositiveMatrixMeasure
end SecretKey

end

end OAI
