import Mathlib
import OAI.Analysis.HardSphere.Conditioning.FiberDisintegrate

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {E I : Type*} [MeasurableSpace E] [Fintype I]
variable {X : I→Type*} [∀i,MeasurableSpace (X i)]

def blockGlue (p : I→Prop) [DecidablePred p]
    (z : (E×(∀i : {i // ¬p i},X i))×(∀i : {i // p i},X i)) : E×(∀i,X i) :=
  (z.1.1,(MeasurableEquiv.piEquivPiSubtypeProd X p).symm (z.2,z.1.2))

lemma blockGlue_preserving (μ : Measure E) [SFinite μ] (ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (ν i)]
    (p : I→Prop) [DecidablePred p] :
    MeasurePreserving (blockGlue (E:=E) p)
      ((μ.prod (Measure.pi fun i : {i // ¬p i} ↦ ν i)).prod (Measure.pi fun i : {i // p i} ↦ ν i))
      (μ.prod (Measure.pi ν)) := by
  have h₁ := measurePreserving_prodAssoc μ (Measure.pi fun i : {i // ¬p i} ↦ ν i) (Measure.pi fun i : {i // p i} ↦ ν i)
  have h₂ := (MeasurePreserving.id μ).prod (Measure.measurePreserving_swap
    (μ:=Measure.pi fun i : {i // ¬p i} ↦ ν i) (ν:=Measure.pi fun i : {i // p i} ↦ ν i))
  have h₃ := (MeasurePreserving.id μ).prod ((measurePreserving_piEquivPiSubtypeProd ν p).symm (MeasurableEquiv.piEquivPiSubtypeProd X p))
  exact h₃.comp (h₂.comp h₁)

omit [Fintype I] in
lemma blockGlue_measurable (p : I→Prop) [DecidablePred p] : Measurable (blockGlue (E:=E) (X:=X) p) :=
  measurable_fst.fst.prodMk ((MeasurableEquiv.piEquivPiSubtypeProd X p).symm.measurable.comp (measurable_snd.prodMk measurable_fst.snd))

def blockEvent (p : I→Prop) [DecidablePred p] (B : Set (E×(∀i,X i))) := blockGlue p ⁻¹' B

def exposedLaw (μ : Measure E) [SFinite μ] (ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (ν i)]
    (p : I→Prop) [DecidablePred p] (B : Set (E×(∀i,X i))) : Measure (E×(∀i : {i // ¬p i},X i)) :=
  (μ.prod (Measure.pi fun i : {i // ¬p i} ↦ ν i)).withDensity
    (fun w ↦ fiberRestrict (Kernel.const _ (Measure.pi fun i : {i // p i} ↦ ν i)) (blockEvent p B) w univ)

lemma exposed_block_reconstruct (μ : Measure E) [SFinite μ] (ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (ν i)]
    (p : I→Prop) [DecidablePred p] {B : Set (E×(∀i,X i))} (hB : MeasurableSet B)
    [SFinite (exposedLaw μ ν p B)] :
    ((exposedLaw μ ν p B).compProd
       (fiberNormalize (Kernel.const _ (Measure.pi fun i : {i // p i} ↦ ν i)) (blockEvent p B))).map (blockGlue p)=
      (μ.prod (Measure.pi ν)).restrict B := by
  have hC : MeasurableSet (blockEvent p B) := hB.preimage (blockGlue_measurable p)
  have h := fiber_disintegrate (μ.prod (Measure.pi fun i : {i // ¬p i} ↦ ν i))
    (Kernel.const _ (Measure.pi fun i : {i // p i} ↦ ν i)) hC
  change ((exposedLaw μ ν p B).compProd _).map _=_
  rw [show (exposedLaw μ ν p B).compProd (fiberNormalize (Kernel.const _ (Measure.pi fun i : {i // p i} ↦ ν i)) (blockEvent p B))=
      ((μ.prod (Measure.pi fun i : {i // ¬p i} ↦ ν i)).prod (Measure.pi fun i : {i // p i} ↦ ν i)).restrict (blockEvent p B) by simpa only [Measure.compProd_const,exposedLaw] using h]
  exact ((blockGlue_preserving μ ν p).restrict_preimage hB).map_eq

lemma exposed_block_positive (μ : Measure E) [SFinite μ] (ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (ν i)]
    (p : I→Prop) [DecidablePred p] {B : Set (E×(∀i,X i))} (hB : MeasurableSet B) :
    ∀ᵐw ∂exposedLaw μ ν p B,0<(Measure.pi fun i : {i // p i} ↦ ν i) {v | blockGlue p (w,v)∈B} := by
  exact exposed_mass_positive (μ.prod (Measure.pi fun i : {i // ¬p i} ↦ ν i))
    (Kernel.const _ (Measure.pi fun i : {i // p i} ↦ ν i)) (hB.preimage (blockGlue_measurable p))

end HardSphere.Comparison

end
end

end

end OAI
