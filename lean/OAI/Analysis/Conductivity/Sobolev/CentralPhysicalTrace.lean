import Mathlib
import OAI.Analysis.Conductivity.Geometry.PhysicalCollarTrace
import OAI.Analysis.Conductivity.Branching.ChildCoordinateAnalysis

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory UnitAddTorus

def centralTraceConstant : ℝ := ((1+1/centralThickness)*physicalRayConstant)*(sourceScale^3)⁻¹

lemma centralTraceConstant_pos : 0<centralTraceConstant := by
  have := physicalRayConstant_pos
  dsimp [centralTraceConstant,centralThickness,sourceScale]
  positivity

lemma centralTraceConstant_parent : (1+1/centralThickness)*physicalRayConstant≤centralTraceConstant := by
  have hh := physicalRayConstant_pos
  dsimp [centralTraceConstant,centralThickness,sourceScale]
  nlinarith

lemma central_parent_trace {f : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    (∫ x : UnitAddTorus (Fin 2),(f (sourceAngularCollar centralThickness x))^2)≤
      centralTraceConstant*(∫ y in centralPhysical,sourcePhysicalEnergy f y) := by
  have hh := sourceAngular_physical_trace_forward hf centralPhysical_compact centralThickness
    (η:=centralThickness) (by norm_num [centralThickness]) (by norm_num [centralThickness])
    (by norm_num [centralThickness]) (fun i j y hy => by
      obtain ⟨x,hx,rfl⟩ := hy
      apply sourceParentCollar_central i j
      simpa [two_mul] using hx)
  have hn : 0≤∫ y in centralPhysical,sourcePhysicalEnergy f y := integral_nonneg (sourcePhysicalEnergy_nonneg f)
  exact hh.trans (mul_le_mul_of_nonneg_right centralTraceConstant_parent hn)

lemma central_child_trace {f : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    {σ : ℝ} (hσ : σ=1 ∨ σ= -1) :
    (∫ x : UnitAddTorus (Fin 2),(f (sourceChildCoordinates σ (sourceAngularCollar (-centralThickness) x)))^2)≤
      centralTraceConstant*(∫ y in centralPhysical,sourcePhysicalEnergy f y) := by
  let K := sourceChildCoordinates σ ⁻¹' centralPhysical
  have hK : IsCompact K := (sourceChildHomeomorph σ).isCompact_preimage.mpr centralPhysical_compact
  have hfc := hf.comp (sourceChildCoordinates_contDiff σ)
  have hh := sourceAngular_physical_trace_backward hfc hK (-centralThickness)
    (η:=centralThickness) (by norm_num [centralThickness]) (by norm_num [centralThickness])
    (by norm_num [centralThickness]) (fun i j y hy => by
      obtain ⟨x,hx,rfl⟩ := hy
      apply sourceChildCollar_central i j hσ
      convert hx using 1; ring_nf)
  have hmono : (∫ y in K,sourcePhysicalEnergy (f ∘ sourceChildCoordinates σ) y)≤
      ∫ y in K,sourcePhysicalEnergy f (sourceChildCoordinates σ y) := by
    apply integral_mono
      ((continuous_sourcePhysicalEnergy hfc).continuousOn.integrableOn_compact hK)
      (((continuous_sourcePhysicalEnergy hf).comp (sourceChildCoordinates_contDiff σ).continuous).continuousOn.integrableOn_compact hK)
      (sourceChild_energy hf σ)
  have he := integral_sourceChild_preimage σ centralPhysical_compact (sourcePhysicalEnergy f)
  change (∫ y in K,sourcePhysicalEnergy f (sourceChildCoordinates σ y))=_ at he
  rw [he] at hmono
  exact hh.trans (by
    have hm := mul_le_mul_of_nonneg_left hmono (show 0≤(1+1/centralThickness)*physicalRayConstant by
      have := physicalRayConstant_pos; norm_num [centralThickness]; positivity)
    simpa [centralTraceConstant,mul_assoc] using hm)

def centralBoundary (i : Fin 3) (x : UnitAddTorus (Fin 2)) : Box3 :=
  sourcePairCoordinates (![sourceAngularCollar centralThickness x,
    sourceChildCoordinates 1 (sourceAngularCollar (-centralThickness) x),
    sourceChildCoordinates (-1) (sourceAngularCollar (-centralThickness) x)] i)

lemma continuous_centralBoundary (i : Fin 3) : Continuous (centralBoundary i) := by
  fin_cases i <;> apply sourcePairCLE.continuous.comp
  · exact continuous_sourceAngularCollar _
  · exact (sourceChildCoordinates_contDiff 1).continuous.comp (continuous_sourceAngularCollar _)
  · exact (sourceChildCoordinates_contDiff (-1)).continuous.comp (continuous_sourceAngularCollar _)

lemma central_physical_trace {f : Box3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (i : Fin 3) :
    (∫ x : UnitAddTorus (Fin 2),(f (centralBoundary i x))^2)≤
      centralTraceConstant*(∫ z in centralClosed,192*cubeEnergyDensity f z+2*(f z)^2) := by
  have hfc : ContDiff ℝ (↑(⊤ : ℕ∞)) (f ∘ sourcePairCoordinates) := hf.comp sourcePairCLE.contDiff
  have ht : (∫ x : UnitAddTorus (Fin 2),(f (centralBoundary i x))^2)≤
      centralTraceConstant*(∫ y in centralPhysical,sourcePhysicalEnergy (f ∘ sourcePairCoordinates) y) := by
    fin_cases i
    · exact central_parent_trace hfc
    · exact central_child_trace hfc (Or.inl rfl)
    · exact central_child_trace hfc (Or.inr rfl)
  have hm : (∫ y in centralPhysical,sourcePhysicalEnergy (f ∘ sourcePairCoordinates) y)≤
      ∫ y in centralPhysical,192*cubeEnergyDensity f (sourcePairCoordinates y)+2*(f (sourcePairCoordinates y))^2 := by
    apply integral_mono
      ((continuous_sourcePhysicalEnergy hfc).continuousOn.integrableOn_compact centralPhysical_compact)
      (((continuous_const.mul ((continuous_cubeEnergyDensity hf).comp sourcePairCLE.continuous)).add
        (continuous_const.mul ((hf.continuous.comp sourcePairCLE.continuous).pow 2))).continuousOn.integrableOn_compact centralPhysical_compact)
      (sourcePair_energy hf)
  rw [integral_centralPhysical (fun z => 192*cubeEnergyDensity f z+2*(f z)^2)] at hm
  exact ht.trans (mul_le_mul_of_nonneg_left hm centralTraceConstant_pos.le)

end ScalarConductivity

end

end OAI
