import Mathlib

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle Function
open scoped Topology ContDiff
variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace F M]

@[instance_reducible]
def reModelChartedSpace (L : F ≃L[ℝ] E) : ChartedSpace E M where
  atlas := (fun e : OpenPartialHomeomorph M F => e.trans L.toHomeomorph.toOpenPartialHomeomorph) '' atlas F M
  chartAt x := (chartAt F x).trans L.toHomeomorph.toOpenPartialHomeomorph
  mem_chart_source x := by simp
  chart_mem_atlas x := ⟨chartAt F x,chart_mem_atlas _ _,rfl⟩

lemma reModel_isManifold (L : F ≃L[ℝ] E) [IsManifold 𝓘(ℝ,F) ∞ M] :
    @IsManifold ℝ _ E _ _ E _ 𝓘(ℝ,E) ∞ M _ (reModelChartedSpace (M:=M) L) := by
  let := reModelChartedSpace (M:=M) L
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨e,he,rfl⟩ ⟨f,hf,rfl⟩
  have h := (contDiffGroupoid ∞ 𝓘(ℝ,F)).compatible he hf
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at h
  have h₁ : ContDiffOn ℝ ∞ ((e.symm.trans f) : F → F) (e.symm.trans f).source := by
    simpa only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      range_id, preimage_id, inter_univ, id_comp, comp_id] using h.1
  have hh := L.contDiff.comp_contDiffOn (h₁.comp L.symm.contDiff.contDiffOn
    (mapsTo_preimage _ _))
  have hc : (L.toHomeomorph.toOpenPartialHomeomorph : F → E) = L := rfl
  have hcs : (L.toHomeomorph.toOpenPartialHomeomorph.symm : E → F) = L.symm := rfl
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    range_id, preimage_id, inter_univ, id_comp, comp_id,
    OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    Homeomorph.toOpenPartialHomeomorph_source, Homeomorph.toOpenPartialHomeomorph_target,
    hc, hcs, preimage_univ, preimage_inter, preimage_comp, univ_inter, comp_assoc] using hh

end


section
open Set Filter Manifold Bundle Function
open scoped Topology ContDiff
variable {E F G M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace M] [ChartedSpace F M]
  [TopologicalSpace N] [ChartedSpace G N]

lemma contMDiff_reModel_source (L : F ≃L[ℝ] E) {f : M → N}
    (hf : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,G) ∞ f) :
    letI := reModelChartedSpace (M:=M) L
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,G) ∞ f := by
  let := reModelChartedSpace (M:=M) L
  intro x
  have h := (contMDiffAt_iff.mp (hf x))
  rw [contMDiffAt_iff]
  refine ⟨h.1,?_⟩
  simp only [modelWithCornersSelf_coe, range_id, contDiffWithinAt_univ] at h ⊢
  simp only [extChartAt, OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id_comp, comp_id] at h ⊢
  have hh := (show ContDiffAt ℝ ∞ _ (L.symm (L (chartAt F x x))) from by simpa using h.2).comp
    (L (chartAt F x x)) L.symm.contDiff.contDiffAt
  have hc : (chartAt E x : M → E) = L ∘ (chartAt F x) := rfl
  have hcs : ((chartAt E x).symm : E → M) = (chartAt F x).symm ∘ L.symm := rfl
  rw [hc,hcs]
  simpa only [comp_assoc,comp_apply] using hh

lemma contMDiff_reModel_target (L : F ≃L[ℝ] E) {f : N → M}
    (hf : ContMDiff 𝓘(ℝ,G) 𝓘(ℝ,F) ∞ f) :
    letI := reModelChartedSpace (M:=M) L
    ContMDiff 𝓘(ℝ,G) 𝓘(ℝ,E) ∞ f := by
  let := reModelChartedSpace (M:=M) L
  intro x
  have h := (contMDiffAt_iff.mp (hf x))
  rw [contMDiffAt_iff]
  refine ⟨h.1,?_⟩
  simp only [modelWithCornersSelf_coe, range_id, contDiffWithinAt_univ] at h ⊢
  simp only [extChartAt, OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id_comp, comp_id] at h ⊢
  have hh := L.contDiff.contDiffAt.comp (chartAt G x x) h.2
  have hc : (chartAt E (f x) : M → E) = L ∘ (chartAt F (f x)) := rfl
  rw [hc]
  simpa only [comp_assoc] using hh

end


section
open Set Filter Manifold Bundle Function
open scoped Topology ContDiff
variable {E F G M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace M] [ChartedSpace F M]
  [TopologicalSpace N] [ChartedSpace G N]
lemma mfderiv_reModel_source (L : F ≃L[ℝ] E) {f : M → N}
    (hf : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,G) ∞ f) (x : M) :
    let D : F →L[ℝ] G := mfderiv 𝓘(ℝ,F) 𝓘(ℝ,G) f x
    letI := reModelChartedSpace (M:=M) L
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,G) f x = D.comp L.symm.toContinuousLinearMap := by
  let D : F →L[ℝ] G := mfderiv 𝓘(ℝ,F) 𝓘(ℝ,G) f x
  have hd := (hf.mdifferentiable (by simp) x).hasMFDerivAt
  rw [HasMFDerivAt] at hd
  simp only [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, range_id, hasFDerivWithinAt_univ,
    id_comp, comp_id] at hd
  change ContinuousAt f x ∧ HasFDerivAt (↑(chartAt G (f x)) ∘ f ∘ ↑(chartAt F x).symm) D (chartAt F x x) at hd
  let := reModelChartedSpace (M:=M) L
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,G) f x = D.comp L.symm.toContinuousLinearMap
  apply HasMFDerivAt.mfderiv
  change ContinuousAt f x ∧ HasFDerivWithinAt _ _ _ _
  refine ⟨hd.1,?_⟩
  simp only [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, range_id, hasFDerivWithinAt_univ,
    id_comp, comp_id]
  change HasFDerivAt (↑(chartAt G (f x)) ∘ f ∘ ↑(chartAt E x).symm)
    (D.comp L.symm.toContinuousLinearMap : E →L[ℝ] G) (chartAt E x x)
  have hc : (chartAt E x : M → E) = L ∘ (chartAt F x) := rfl
  have hcs : ((chartAt E x).symm : E → M) = (chartAt F x).symm ∘ L.symm := rfl
  rw [hc,hcs]
  have hh := (show HasFDerivAt _ D (L.symm (L (chartAt F x x))) from by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hd.2).comp
      (L (chartAt F x x)) L.symm.toContinuousLinearMap.hasFDerivAt
  simpa only [comp_assoc,comp_apply] using hh
end


open Set Filter Manifold Bundle Function
open scoped Topology ContDiff
variable {E F G M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace M] [ChartedSpace F M]
  [TopologicalSpace N] [ChartedSpace G N]
lemma mfderiv_reModel_target (L : F ≃L[ℝ] E) {f : N → M}
    (hf : ContMDiff 𝓘(ℝ,G) 𝓘(ℝ,F) ∞ f) (x : N) :
    let D : G →L[ℝ] F := mfderiv 𝓘(ℝ,G) 𝓘(ℝ,F) f x
    letI := reModelChartedSpace (M:=M) L
    mfderiv 𝓘(ℝ,G) 𝓘(ℝ,E) f x = L.toContinuousLinearMap.comp D := by
  let D : G →L[ℝ] F := mfderiv 𝓘(ℝ,G) 𝓘(ℝ,F) f x
  have hd := (hf.mdifferentiable (by simp) x).hasMFDerivAt
  rw [HasMFDerivAt] at hd
  simp only [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, range_id, hasFDerivWithinAt_univ,
    id_comp, comp_id] at hd
  change ContinuousAt f x ∧ HasFDerivAt (↑(chartAt F (f x)) ∘ f ∘ ↑(chartAt G x).symm) D (chartAt G x x) at hd
  let := reModelChartedSpace (M:=M) L
  change mfderiv 𝓘(ℝ,G) 𝓘(ℝ,E) f x = L.toContinuousLinearMap.comp D
  apply HasMFDerivAt.mfderiv
  change ContinuousAt f x ∧ HasFDerivWithinAt _ _ _ _
  refine ⟨hd.1,?_⟩
  simp only [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, range_id, hasFDerivWithinAt_univ,
    id_comp, comp_id]
  change HasFDerivAt (↑(chartAt E (f x)) ∘ f ∘ ↑(chartAt G x).symm)
    (L.toContinuousLinearMap.comp D : G →L[ℝ] E) (chartAt G x x)
  have hc : (chartAt E (f x) : M → E) = L ∘ (chartAt F (f x)) := rfl
  rw [hc]
  have hh := L.toContinuousLinearMap.hasFDerivAt.comp (chartAt G x x) hd.2
  simpa only [comp_assoc,comp_apply,ContinuousLinearEquiv.coe_coe] using hh

end YauCounterexamples
end

end OAI
