import Mathlib
import OAI.Analysis.Conductivity.Branching.ParentLocalizedJet

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : ℝ} (ha : a<0)
  {χ : (Fin 3 → ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)
  (hχb : ∀ x,|χ x|≤1)
  (hχs : tsupport χ⊆sourceClosedCollarBand 0 (2*centralThickness))

include hχb hχs in
lemma parentLocalJetCLM_smooth_H10 (f : centralSmoothFunctions) :
    parentLocalJetCLM s hs ha hχ hc (centralEmbedL s f)∈zeroTraceAmbient := by
  have hq := (central_smooth f).comp sourcePairCLE.contDiff
  obtain ⟨w,hw,hwe⟩ := smoothCollarTrace_localJoined_H1 hs hq hχ hc hχb ha.ne
    (show (0:ℝ)<centralThickness by norm_num [centralThickness])
    (show -(1:ℝ)/100≤centralThickness-centralThickness by norm_num)
    (show centralThickness+centralThickness≤(1:ℝ)/100 by norm_num [centralThickness])
    (by simpa only [sub_self,two_mul] using hχs)
  dsimp only at hwe
  rw [central_parent_trace_eq s f] at hwe
  have he : parentLocalJetCLM s hs ha hχ hc (centralEmbedL s f)=w.val := by
    apply Lp.ext
    filter_upwards [parentLocalJetCLM_smooth_ae s hs ha hχ hc hχs f,hwe] with x hx hwx
    rw [hx]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hwx.1.symm
    · exact (hwx.2 j).symm
  rw [he]
  exact hw

include hχb hχs in

theorem parentLocalJetCLM_central_H10 (u : centralEnergySpace s) :
    parentLocalJetCLM s hs ha hχ hc u.val∈zeroTraceAmbient := by
  let T := (zeroTraceAmbient.comap (parentLocalJetCLM s hs ha hχ hc).toLinearMap)
  have ht : IsClosed (T : Set (CentralAmbient s)) :=
    (Submodule.isClosed_topologicalClosure (Submodule.span ℝ compactSmoothJets)).preimage
      (parentLocalJetCLM s hs ha hχ hc).continuous
  have hr : LinearMap.range (centralEmbedL s)≤T := by
    rintro z ⟨f,rfl⟩
    exact parentLocalJetCLM_smooth_H10 s hs ha hχ hc hχb hχs f
  exact (Submodule.topologicalClosure_minimal _ hr ht) u.property

def parentCompletionJoin : centralEnergySpace s →L[ℝ] H1 :=
  ((parentLocalJetCLM s hs ha hχ hc).comp (centralEnergySpace s).subtypeL).codRestrict H1Space
    (fun u => zeroTraceAmbient_le_H1Space (parentLocalJetCLM_central_H10 s hs ha hχ hc hχb hχs u))

lemma parentCompletionJoin_mem_H10 (u : centralEnergySpace s) :
    parentCompletionJoin s hs ha hχ hc hχb hχs u∈H10 :=
  parentLocalJetCLM_central_H10 s hs ha hχ hc hχb hχs u

end

open Set MeasureTheory Filter Topology
open scoped ENNReal

variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure X} {ν : Measure Y} (e : X ≃ᵐ Y) {c : ℝ≥0∞}
  (hc : c≠∞) (hmap : Measure.map e μ≤c • ν)

def lpBoundedPullbackCLM : Lp E 2 ν →L[ℝ] Lp E 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℝ e (show MeasurePreserving e μ (Measure.map e μ) from ⟨e.measurable,rfl⟩)).toContinuousLinearMap.comp
    (Lp.LpToLpOfMeasureLeSMul (c:=c) hc hmap)

lemma lpBoundedPullbackCLM_ae (f : Lp E 2 ν) :
    lpBoundedPullbackCLM e hc hmap f=ᵐ[μ] (fun x => f (e x)) := by
  apply (Lp.coeFn_compMeasurePreserving _ (show MeasurePreserving e μ (Measure.map e μ) from ⟨e.measurable,rfl⟩)).trans
  exact (show MeasurePreserving e μ (Measure.map e μ) from ⟨e.measurable,rfl⟩).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_LpToLpOfMeasureLeSMul hc hmap f)

lemma lpBoundedPullbackCLM_ae_of_ae (hq : Measure.QuasiMeasurePreserving e μ ν)
    (f : Lp E 2 ν) {g : Y → E} (hg : f=ᵐ[ν] g) :
    lpBoundedPullbackCLM e hc hmap f=ᵐ[μ] (fun x => g (e x)) :=
  (lpBoundedPullbackCLM_ae e hc hmap f).trans (hq.ae_eq_comp hg)

lemma sourceChildCoordinates_translate (σ : ℝ) :
    sourceChildCoordinates σ=(fun y : Fin 3 → ℝ => y+![σ*sourceOffset,0,0]) ∘ sourceChildDerivative := by
  funext y
  rw [Function.comp_apply,sourceChildDerivative_apply]
  ext i
  fin_cases i <;> simp [sourceChildCoordinates]

lemma sourceChildCoordinates_map_volume (σ : ℝ) :
    Measure.map (sourceChildCoordinates σ) volume=ENNReal.ofReal ((sourceScale^3)⁻¹) • volume := by
  have hd : sourceChildDerivative.det≠0 := by rw [sourceChildDerivative_det]; norm_num [sourceScale]
  rw [sourceChildCoordinates_translate]
  rw [←Measure.map_map (g:=fun y : Fin 3 → ℝ => y+![σ*sourceOffset,0,0])
    (f:=sourceChildDerivative) (continuous_id.add continuous_const).measurable sourceChildDerivative.continuous.measurable]
  have hm := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin 3 → ℝ)) hd
  change Measure.map sourceChildDerivative volume=ENNReal.ofReal |sourceChildDerivative.det⁻¹| • volume at hm
  rw [hm,Measure.map_smul _ (measurePreserving_add_right volume ![σ*sourceOffset,0,0]).measurable.aemeasurable,
    (measurePreserving_add_right volume ![σ*sourceOffset,0,0]).map_eq]
  congr 2
  rw [sourceChildDerivative_det,inv_neg,abs_neg,abs_of_nonneg]
  exact inv_nonneg.mpr (by norm_num [sourceScale])

lemma sourceChildCoordinates_quasi (σ : ℝ) :
    Measure.QuasiMeasurePreserving (sourceChildCoordinates σ) volume volume := by
  refine ⟨(sourceChildHomeomorph σ).measurable,?_⟩
  rw [sourceChildCoordinates_map_volume]
  exact Measure.smul_absolutelyContinuous

def sourceChildPullbackCLM (σ : ℝ) : Lp E 2 (volume : Measure (Fin 3 → ℝ)) →L[ℝ]
    Lp E 2 (volume : Measure (Fin 3 → ℝ)) :=
  lpBoundedPullbackCLM (sourceChildHomeomorph σ).toMeasurableEquiv ENNReal.ofReal_ne_top
    (le_of_eq (sourceChildCoordinates_map_volume σ))

lemma sourceChildPullbackCLM_ae (σ : ℝ) (f : Lp E 2 (volume : Measure (Fin 3 → ℝ))) :
    sourceChildPullbackCLM σ f=ᵐ[volume] (fun y => f (sourceChildCoordinates σ y)) :=
  lpBoundedPullbackCLM_ae _ _ _ f

end ScalarConductivity

end

end OAI
