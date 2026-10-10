import Mathlib
import OAI.Probability.Perceptron.Cascade.PoissonLaplace

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

variable {S : Type*} [MeasurableSpace S]

def indexedFiniteCloud (a : ℕ × (ℕ → S)) : Measure S :=
  finitePointMeasure a.1 (fun i => a.2 i.val)

lemma indexedFiniteCloud_measurable : Measurable (indexedFiniteCloud (S := S)) := by
  have h : Measurable (fun a : (ℕ → S) × ℕ => indexedFiniteCloud (a.2,a.1)) := by
    apply measurable_from_prod_countable_left
    intro n
    exact (finitePointMeasure_measurable n).comp (Measurable.of_eval fun index => measurable_pi_apply index.val)
  exact h.comp measurable_swap

lemma iid_prefix_law (ν : Measure S) [IsProbabilityMeasure ν] (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => ν)).map (fun x (i : Fin n) => x i.val) =
      Measure.pi (fun _ : Fin n => ν) := by
  rw [Measure.map_infinitePi_infinitePi_of_inj (f := Fin.val) Fin.val_injective,
    Measure.infinitePi_eq_pi]

lemma indexedFiniteCloud_law (r : ℝ≥0) (ν : Measure S) [IsProbabilityMeasure ν] :
    ((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ => ν))).map indexedFiniteCloud =
      finitePoissonLaw r ν := by
  rw [← Measure.sum_smul_dirac (poissonMeasure r),Measure.prod_sum_left,
    Measure.map_sum indexedFiniteCloud_measurable.aemeasurable]
  simp_rw [Measure.prod_smul_left,Measure.map_smul _ indexedFiniteCloud_measurable.aemeasurable,Measure.dirac_prod,
    Measure.map_map indexedFiniteCloud_measurable measurable_prodMk_left]
  unfold finitePoissonLaw
  congr 1
  funext n
  congr 1
  rw [← iid_prefix_law ν n,Measure.map_map (finitePointMeasure_measurable n) (by fun_prop)]
  rfl

def indexedPoissonMeasure (a : ℕ → ℕ × (ℕ → S)) : Measure S :=
  Measure.sum (fun i => indexedFiniteCloud (a i))

lemma indexedPoissonMeasure_measurable : Measurable (indexedPoissonMeasure (S := S)) :=
  measureSum_measurable.comp (Measurable.of_eval fun index =>
    indexedFiniteCloud_measurable.comp (measurable_pi_apply index))

lemma indexedPoissonMeasure_law (r : ℕ → ℝ≥0) (ν : ℕ → Measure S)
    [∀ i, IsProbabilityMeasure (ν i)] :
    (Measure.infinitePi (fun i => (poissonMeasure (r i)).prod
      (Measure.infinitePi (fun _ : ℕ => ν i)))).map indexedPoissonMeasure =
        countablePoissonLaw r ν := by
  unfold indexedPoissonMeasure countablePoissonLaw
  have hm : Measurable (fun a : ℕ → ℕ × (ℕ → S) => fun i => indexedFiniteCloud (a i)) :=
    Measurable.of_eval fun index => indexedFiniteCloud_measurable.comp (measurable_pi_apply index)
  change (Measure.infinitePi (fun i => (poissonMeasure (r i)).prod
    (Measure.infinitePi (fun _ : ℕ => ν i)))).map
      ((fun η : ℕ → Measure S => Measure.sum η) ∘ (fun a : ℕ → ℕ × (ℕ → S) => fun i => indexedFiniteCloud (a i))) = _
  rw [← Measure.map_map measureSum_measurable hm,Measure.infinitePi_map_pi]
  · simp_rw [indexedFiniteCloud_law]
  · exact fun _ => indexedFiniteCloud_measurable

lemma indexedPoissonMeasure_canonical_law [Nonempty S] (κ : Measure S) [SFinite κ] :
    (Measure.infinitePi (fun i =>
      (poissonMeasure (((sfiniteSeq κ i) univ).toNNReal)).prod
      (Measure.infinitePi (fun _ : ℕ => finiteIntensityMarks (sfiniteSeq κ i))))).map
        indexedPoissonMeasure = poissonRandomMeasureLaw κ :=
  indexedPoissonMeasure_law _ _

end SphericalPerceptronFreeEnergy
end

end OAI
