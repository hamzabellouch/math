import OAI.Probability.GaussianReplacement.StreamVolume
import OAI.Probability.GaussianRegression.Sphere

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
universe u
namespace NoiselessRegression
open InnerProductSpace

section SphereBounds
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end SphereBounds

open scoped Pointwise
section MoreSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end MoreSphere

section FubiniAux
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
lemma ae_fiber_aemeasurable {f : X × Y → Z} (hf : AEMeasurable f (μ.prod ν)) :
    ∀ᵐ y ∂ν, AEMeasurable (fun x => f (x,y)) μ := by
  have he := Measure.ae_ae_of_ae_prod hf.prod_swap.ae_eq_mk
  filter_upwards [he] with y hy
  have hm : Measurable (fun x => hf.prod_swap.mk _ (y,x)) :=
    hf.prod_swap.measurable_mk.comp (measurable_const.prodMk measurable_id)
  exact hm.aemeasurable.congr (Filter.EventuallyEq.symm hy)

lemma prod_null_set_bound {S : Set (X × Y)} (hS : NullMeasurableSet S (μ.prod ν))
    {c : ℝ≥0∞} (h : ∀ᵐ y ∂ν, μ {x | (x,y) ∈ S} ≤ c) :
    (μ.prod ν) S ≤ c * ν univ := by
  have hm : AEMeasurable (S.indicator (fun _ => (1 : ℝ≥0∞))) (μ.prod ν) :=
    aemeasurable_const.indicator₀ hS
  rw [← one_mul ((μ.prod ν) S), ← lintegral_indicator_const₀ hS 1, lintegral_prod_symm _ hm]
  apply (lintegral_mono_ae ?_).trans_eq (lintegral_const c)
  filter_upwards [h, ae_fiber_aemeasurable hm] with y hy hmy
  have hs : NullMeasurableSet {x | (x,y) ∈ S} μ := by
    have heq : {x | (x,y) ∈ S} = {x | S.indicator (fun _ => (1 : ℝ≥0∞)) (x,y) = 1} := by
      ext x
      by_cases hx : (x,y) ∈ S <;> simp [hx]
    rw [heq]
    exact nullMeasurableSet_eq_fun hmy aemeasurable_const
  change (∫⁻ x, ({x | (x,y) ∈ S}).indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ) ≤ c
  simpa [lintegral_indicator_const₀ hs] using hy
end FubiniAux

instance sampleLaw_probability (d T : ℕ) : IsProbabilityMeasure (sampleLaw d T) := by
  unfold sampleLaw
  infer_instance
instance uniformSphere_probability (d : ℕ) [NeZero d] : IsProbabilityMeasure (uniformSphere d) := by
  change IsProbabilityMeasure (sphereLaw (E := Vector d))
  infer_instance

end NoiselessRegression

end

end OAI
