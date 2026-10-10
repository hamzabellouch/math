import Mathlib

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise

namespace LogConcaveSampling

lemma map_prod_eq_of_second_fiber_law {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    {μ : Measure A} {ν : Measure B} [SFinite μ] [SFinite ν]
    {f g : A × B → C} (hf : Measurable f) (hg : Measurable g)
    (h : ∀ a, ν.map (fun b => f (a,b)) = ν.map (fun b => g (a,b))) :
    (μ.prod ν).map f = (μ.prod ν).map g := by
  ext s hs
  rw [Measure.map_apply hf hs, Measure.map_apply hg hs,
    Measure.prod_apply (hs.preimage hf), Measure.prod_apply (hs.preimage hg)]
  apply lintegral_congr
  intro a
  have ha := congrArg (fun κ : Measure C => κ s) (h a)
  rw [Measure.map_apply (f := fun b => f (a,b)) (by fun_prop) hs,
    Measure.map_apply (f := fun b => g (a,b)) (by fun_prop) hs] at ha
  exact ha

end LogConcaveSampling

end LowerProof
end
end
end

end OAI
