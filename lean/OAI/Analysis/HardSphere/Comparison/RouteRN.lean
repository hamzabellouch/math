import Mathlib
import OAI.Analysis.HardSphere.Allocation.PhysicalRouteAuxiliary

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Comparison

lemma piSubtype_measurableEmbedding {I : Type*} [Countable I]
    {X : I→Type*} [∀i,MeasurableSpace (X i)] (A : ∀i,Set (X i))
    (hA : ∀i,MeasurableSet (A i)) :
    MeasurableEmbedding (fun z : ∀i,A i ↦ fun i ↦ (z i).val) := by
  let f : (∀i,A i)→∀i,X i := fun z i ↦ (z i).val
  have hr : range f={z | ∀i,z i∈A i} := by
    ext z
    constructor
    · rintro ⟨w,rfl⟩ i
      exact (w i).property
    · intro hz
      exact ⟨fun i ↦ ⟨z i,hz i⟩,rfl⟩
  let g : range f→∀i,A i := fun z i ↦ ⟨z.val i,by
    exact ((Set.ext_iff.mp hr z.val).mp z.property) i⟩
  apply MeasurableEmbedding.of_measurable_inverse_on_range
    (g:=g) (Measurable.of_eval fun i ↦ measurable_subtype_coe.comp (measurable_pi_apply i))
  · rw [hr]
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i ↦ (hA i).preimage (measurable_pi_apply i)
  · exact Measurable.of_eval fun i ↦ ((measurable_pi_apply i).comp measurable_subtype_coe).subtype_mk
  · intro z
    rfl

lemma mapped_likelihood_cross {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P μ ν : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f g : X→ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hμ : μ=P.withDensity f) (hν : ν=P.withDensity g)
    (e : X→Y) (he : MeasurableEmbedding e) :
    (∫⁻y,(μ.map e).rnDeriv (P.map e) y*(ν.map e).rnDeriv (P.map e) y ∂P.map e)=
      ∫⁻x,f x*g x ∂P := by
  rw [he.lintegral_map]
  apply lintegral_congr_ae
  have hf' : (fun x ↦ (μ.map e).rnDeriv (P.map e) (e x))=ᵐ[P] f := by
    refine (he.rnDeriv_map μ P).trans ?_
    rw [hμ]
    exact Measure.rnDeriv_withDensity P hf
  have hg' : (fun x ↦ (ν.map e).rnDeriv (P.map e) (e x))=ᵐ[P] g := by
    refine (he.rnDeriv_map ν P).trans ?_
    rw [hν]
    exact Measure.rnDeriv_withDensity P hg
  exact hf'.mul hg'

end HardSphere.Comparison
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
variable {J : Type*} [Fintype J] [DecidableEq J]
omit [DecidableEq J] in
lemma physicalConfig_embedding {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (d : PhysicalDatum N K M G L) :
    MeasurableEmbedding (routeConfigMap (fun i ↦ (Subtype.val : physicalSlotAllowed hL g m r R C S u particle d i→_))) :=
  piSubtype_measurableEmbedding _ (physicalSlotAllowed_measurable hL g m r R C S u particle d)

variable {N K M G n : ℕ} {L : Length} {hL : L.val=(K:ℝ)} {g : Fin G}
  {m : ℕ} {t r R C S : ℝ} {u : Time} {particle : J↪Fin N}
  {labels : Fin (n+1)↪J} {v : Fin (n+2)→Fin 3→Fin K} {steps : Fin (n+1)→Fin 7}
  {d : PhysicalDatum N K M G L}
lemma PhysicalRouteAux.firstDensity_measurable
    (A : PhysicalRouteAux hL g m t r R C S u particle labels v steps d)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d)) :
    Measurable A.firstDensity := by
  have := physicalOn_probability hL g m t r R C S u particle (v (Fin.last (n+1))) d hp
  exact measurable_conditionalLikelihood _ _ _ _ _ _ _
lemma PhysicalRouteAux.secondDensity_measurable
    (A : PhysicalRouteAux hL g m t r R C S u particle labels v steps d)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d)) :
    Measurable A.secondDensity := by
  have := physicalOn_probability hL g m t r R C S u particle (v 0) d hp
  have : ∀i,IsFiniteKernel (A.backward i) := A.backward_finite
  exact measurable_conditionalLikelihood _ _ _ _ _ _ _

end HardSphere.Groups
end
end

end OAI
