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

lemma map_prod_eq_of_fiber_law {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    {μ : Measure A} {ν : Measure B} [SFinite μ] [SFinite ν]
    {f g : A × B → C} (hf : Measurable f) (hg : Measurable g)
    (h : ∀ b, μ.map (fun a => f (a,b)) = μ.map (fun a => g (a,b))) :
    (μ.prod ν).map f = (μ.prod ν).map g := by
  ext s hs
  rw [Measure.map_apply hf hs, Measure.map_apply hg hs,
    Measure.prod_apply_symm (hs.preimage hf), Measure.prod_apply_symm (hs.preimage hg)]
  apply lintegral_congr
  intro b
  have hb := congrArg (fun κ : Measure C => κ s) (h b)
  rw [Measure.map_apply (f := fun a => f (a,b)) (by fun_prop) hs,
    Measure.map_apply (f := fun a => g (a,b)) (by fun_prop) hs] at hb
  exact hb

lemma map_prod_eq_of_constant_fiber_law {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure μ] [SFinite ν]
    {η : Measure C} {f : A × B → C} (hf : Measurable f)
    (h : ∀ a, ν.map (fun b => f (a,b)) = η) : (μ.prod ν).map f = η := by
  ext s hs
  rw [Measure.map_apply hf hs, Measure.prod_apply (hs.preimage hf)]
  have hh (a : A) : ν (Prod.mk a ⁻¹' (f ⁻¹' s)) = η s := by
    have ha := congrArg (fun κ : Measure C => κ s) (h a)
    rw [Measure.map_apply (f := fun b => f (a,b)) (by fun_prop) hs] at ha
    exact ha
  simp_rw [hh]
  simp

end LogConcaveSampling

end LowerProof
end
end
end

end OAI
