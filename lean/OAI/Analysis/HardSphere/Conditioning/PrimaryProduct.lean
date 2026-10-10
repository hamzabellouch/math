import Mathlib
import OAI.Analysis.HardSphere.Comparison.PhysicalCellReference
import OAI.Analysis.HardSphere.Comparison.PhysicalObservedLaw

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {n : ℕ} {E : Type*} [MeasurableSpace E]
attribute [local instance] permBathSpace permBathSingleton

def adjoinPoint (z : (Fin (n+1)→E)×E) : Option (Fin (n+1))→E :=
  fun i ↦ i.elim z.2 z.1
lemma adjoinPoint_measurable : Measurable (adjoinPoint (n:=n) (E:=E)) := by
  apply Measurable.of_eval
  intro i
  cases i with
  | none => exact measurable_snd
  | some i => exact (measurable_pi_apply i).comp measurable_fst

def cellObservation (b : Bool) (z : (E×(Fin n→E))×E) : E×E×(Fin n→E) :=
  if b then (z.1.1,z.2,z.1.2) else (z.2,z.1.1,z.1.2)
lemma cellObservation_measurable (b : Bool) : Measurable (cellObservation (n:=n) (E:=E) b) := by
  unfold cellObservation
  split_ifs <;> fun_prop

theorem primaryBath_product (P : Measure (Fin (n+1)→E)) [SFinite P]
    (η : Measure E) [SFinite η] (b : Bool) (i : Fin (n+1)) :
    primaryBathKernel b i ∘ₘ (P.prod η).map adjoinPoint =
      (((P.prod (uniformBathOrder n)).map (orderedObservation i)).prod η).map (cellObservation b) := by
  ext s hs
  rw [Measure.bind_apply hs (primaryBathKernel b i).aemeasurable,
    lintegral_map ((primaryBathKernel b i).measurable_coe hs) adjoinPoint_measurable,
    lintegral_prod _ (show AEMeasurable (fun a ↦ primaryBathKernel b i (adjoinPoint a) s) (P.prod η) from
      (((primaryBathKernel b i).measurable_coe hs).comp adjoinPoint_measurable).aemeasurable),
    Measure.map_apply (cellObservation_measurable b) hs,Measure.prod_apply
      ((cellObservation_measurable b) hs)]
  have hm := measurable_measure_prodMk_left (ν:=η) ((cellObservation_measurable b) hs)
  rw [lintegral_map hm (orderedObservation_measurable i),
    lintegral_prod _ (show AEMeasurable (fun a ↦ η (Prod.mk (orderedObservation i a) ⁻¹' cellObservation b ⁻¹' s)) _ from
      (hm.comp (orderedObservation_measurable i)).aemeasurable)]
  apply lintegral_congr
  intro X
  simp_rw [primaryBathKernel_apply]
  have hh : Measurable (fun z : E×Equiv.Perm (Fin n) ↦
      (s.indicator (fun _ ↦ (1:ℝ≥0∞)))
        (orderedPrimaryObservation b i (adjoinPoint (X,z.1),z.2))) :=
    (measurable_const.indicator hs).comp ((orderedPrimaryObservation_measurable b i).comp
      ((adjoinPoint_measurable.comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd))
  convert (lintegral_lintegral_swap (μ:=η) (ν:=uniformBathOrder n)
    (f:=fun e τ ↦ s.indicator (fun _ ↦ (1:ℝ≥0∞))
      (orderedPrimaryObservation b i (adjoinPoint (X,e),τ))) hh.aemeasurable) using 1
  · apply lintegral_congr
    intro e
    rw [←lintegral_indicator_one hs]
    exact lintegral_map (measurable_const.indicator hs)
      (show Measurable (fun τ ↦ orderedPrimaryObservation b i (adjoinPoint (X,e),τ)) from
        (orderedPrimaryObservation_measurable b i).comp (measurable_const.prodMk measurable_id))
  · apply lintegral_congr
    intro τ
    have he : (fun e ↦ orderedPrimaryObservation b i (adjoinPoint (X,e),τ))=
        (fun e ↦ cellObservation b (orderedObservation i (X,τ),e)) := by
      funext e
      cases b <;> rfl
    change η ((fun e ↦ cellObservation b (orderedObservation i (X,τ),e)) ⁻¹' s)=_
    have hm : Measurable (fun e ↦ cellObservation b (orderedObservation i (X,τ),e)) :=
      (cellObservation_measurable b).comp measurable_prodMk_left
    rw [←Measure.map_apply hm hs,←lintegral_indicator_one hs]
    refine (lintegral_map (measurable_const.indicator hs) hm).trans ?_
    exact congrArg (fun f ↦ ∫⁻e,s.indicator (fun _ ↦ (1:ℝ≥0∞)) (f e) ∂η) he.symm

end HardSphere.Comparison
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {n : ℕ} {E : Type*} [MeasurableSpace E]
attribute [local instance] permBathSpace permBathSingleton

lemma prod_restrict_first (P : Measure E) [SFinite P] {Y : Type*} [MeasurableSpace Y]
    (η : Measure Y) [SFinite η] (A : Set E) :
    (P.restrict A).prod η=(P.prod η).restrict (Prod.fst ⁻¹' A) := by
  have H := Measure.prod_restrict (μ:=P) (ν:=η) A univ
  simpa only [Measure.restrict_univ,Set.prod_univ] using H

lemma orderedKernel_restrict (P : Measure (Fin (n+1)→E)) [SFinite P]
    (i : Fin (n+1)) (A : Set E) (hA : MeasurableSet A) :
    (orderedKernel (uniformBathOrder n) i ∘ₘ P).restrict (Prod.fst ⁻¹' A)=
      orderedKernel (uniformBathOrder n) i ∘ₘ P.restrict ((fun X ↦ X i) ⁻¹' A) := by
  rw [orderedKernel_comp,orderedKernel_comp,Measure.restrict_map (orderedObservation_measurable i)
    (hA.preimage measurable_fst),prod_restrict_first]
  rfl

theorem primaryBath_cell_reference (P : Measure (Fin (n+1)→E)) [SFinite P]
    (η : Measure E) [SFinite η] (b : Bool) (i : Fin (n+1))
    (A : Set E) (hA : MeasurableSet A) :
    primaryBathKernel b i ∘ₘ ((P.prod η).map adjoinPoint).restrict ((fun F ↦ F (some i)) ⁻¹' A)=
      (((cellExtraKernel (Y:=Fin n→E) η A univ hA).map (cellObservation b)) ∘ₖ
        orderedKernel (uniformBathOrder n) i) ∘ₘ P := by
  rw [Measure.restrict_map adjoinPoint_measurable (hA.preimage (measurable_pi_apply (some i)))]
  have he : adjoinPoint ⁻¹' ((fun F : Option (Fin (n+1))→E ↦ F (some i)) ⁻¹' A)=
      Prod.fst ⁻¹' ((fun X : Fin (n+1)→E ↦ X i) ⁻¹' A) := rfl
  rw [he,←prod_restrict_first,primaryBath_product,←orderedKernel_comp,
    ←Measure.comp_assoc,←Measure.map_comp _ _ (cellObservation_measurable b),
    cellExtraKernel_comp _ η A univ hA MeasurableSet.univ]
  have he' : {p : (E×(Fin n→E))×E | p.1.1∈A ∧ p.2∈univ}=
      Prod.fst ⁻¹' (Prod.fst ⁻¹' A) := by ext p; simp
  rw [he',←prod_restrict_first,orderedKernel_restrict _ _ A hA]

end HardSphere.Comparison
end
end

end OAI
