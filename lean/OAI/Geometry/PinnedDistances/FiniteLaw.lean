import OAI.Geometry.PinnedDistances.Model

namespace OAI

universe u1 u2 u3

section
noncomputable section
open scoped BigOperators Topology ENNReal
open Filter MeasureTheory
namespace WeakPinned.Bounded

variable {I : Type u1} {X : Type u2} [Fintype I] [MeasurableSpace X] [MeasurableSingletonClass X]

def finiteLaw (w : I → ℝ) (U : I → X) : Measure X :=
  ∑ i,ENNReal.ofReal (w i) • Measure.dirac (U i)

omit [MeasurableSingletonClass X] in
lemma finiteLaw_univ (w : I → ℝ) (U : I → X) (hw : ∀ i,0≤ w i) :
    finiteLaw w U Set.univ=ENNReal.ofReal (∑ i,w i) := by
  simp [finiteLaw,Measure.finsetSum_apply,ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i)]

omit [MeasurableSingletonClass X] in
lemma finiteLaw_probability (w : I → ℝ) (U : I → X)
    (hw : ∀ i,0≤ w i) (hW : ∑ i,w i=1) : IsProbabilityMeasure (finiteLaw w U) := by
  constructor
  rw [finiteLaw_univ w U hw,hW,ENNReal.ofReal_one]

lemma integral_finiteLaw (w : I → ℝ) (U : I → X) (hw : ∀ i,0≤ w i) (f : X → ℝ) :
    ∫ x,f x ∂ finiteLaw w U=∑ i,w i*f (U i) := by
  rw [finiteLaw,integral_finsetSum_measure]
  · simp only [integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal (hw _),smul_eq_mul]
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

lemma finiteLaw_ae (w : I → ℝ) (U : I → X) {p : X → Prop}
    (hp : ∀ i,w i≠0 → p (U i)) : ∀ᵐ x ∂ finiteLaw w U,p x := by
  rw [finiteLaw,ae_finsetSum_measure_iff]
  intro i _
  by_cases h : w i=0
  · simp [h]
  · exact Measure.ae_smul_measure (by simpa only [ae_dirac_eq,Filter.eventually_pure] using hp i h) _

omit [MeasurableSingletonClass X] in
lemma finiteLaw_map {Y : Type u3} [MeasurableSpace Y] (w : I → ℝ) (U : I → X)
    (f : X → Y) (hf : Measurable f) : (finiteLaw w U).map f=finiteLaw w (f ∘ U) := by
  simp only [finiteLaw, Measure.map_finset_sum' hf.aemeasurable,
    Measure.map_smul _ hf.aemeasurable, Measure.map_dirac' hf, Function.comp_def]

def finiteProbability (w : I → ℝ) (U : I → X) (hw : ∀ i,0≤ w i) (hW : ∑ i,w i=1) :
    ProbabilityMeasure X := ⟨finiteLaw w U,finiteLaw_probability w U hw hW⟩

end WeakPinned.Bounded

end
end

end OAI
