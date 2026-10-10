import Mathlib
import OAI.Analysis.Conductivity.Flux.CentralDistribution
import OAI.Analysis.Conductivity.Geometry.SmoothCollarTrace
import OAI.Analysis.Conductivity.Branching.AttachedEndLinear
import OAI.Analysis.Conductivity.Sobolev.LpExtension

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma parentBand_central {y : Fin 3 → ℝ}
    (hy : y∈sourceClosedCollarBand centralThickness (2*centralThickness)) :
    sourcePairCoordinates y∈centralClosed := by
  rw [sourceClosedCollarBand_eq _ _ (by norm_num [centralThickness])
    (by norm_num [centralThickness])] at hy
  rcases mem_iUnion.mp hy with ⟨i, hi⟩
  rcases mem_iUnion.mp hi with ⟨j, hj⟩
  rcases hj with ⟨x, hx, rfl⟩
  exact sourceParentCollar_central i j hx

lemma parentBand_measurable : MeasurableSet (sourceClosedCollarBand centralThickness (2*centralThickness)) :=
  (isCompact_sourceClosedCollarBand (by norm_num [centralThickness]) (by norm_num [centralThickness])).measurableSet

def centralPhysicalWholeCLM : CentralL2 →L[ℝ] Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
  (Lp.compMeasurePreservingₗᵢ ℝ sourcePairMeasurable sourcePair_volume).toContinuousLinearMap.comp
    (lpZeroExtensionCLM centralClosed_compact.measurableSet)

lemma centralPhysicalWholeCLM_smooth_ae (f : centralSmoothFunctions) (i : Fin 4) :
    centralPhysicalWholeCLM (centralSmoothJet f i)=ᵐ[volume]
      (fun y => centralPhysical.indicator (fun y => centralJetField f i (sourcePairCoordinates y)) y) := by
  have he := lpZeroExtensionCLM_ae_of_ae centralClosed_compact.measurableSet
    (centralSmoothJet f i) (centralSmoothJet_ae f i)
  have he' := sourcePair_volume.quasiMeasurePreserving.ae_eq_comp he
  apply (Lp.coeFn_compMeasurePreserving _ sourcePair_volume).trans
  apply he'.trans
  filter_upwards [] with y
  by_cases hy : sourcePairCoordinates y∈centralClosed <;> simp [centralPhysical,hy,sourcePairMeasurable_apply]

def parentCentralComponentCLM (s : Fin 3 → ℝ) (i : Fin 4) :
    CentralAmbient s →L[ℝ] Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
  (lpZeroExtensionCLM parentBand_measurable).comp
    ((lpRestrictionCLM (sourceClosedCollarBand centralThickness (2*centralThickness))).comp
      (centralPhysicalWholeCLM.comp (centralAmbientComponent s i)))

lemma parentCentralComponentCLM_smooth_ae (s : Fin 3 → ℝ) (f : centralSmoothFunctions) (i : Fin 4) :
    parentCentralComponentCLM s i (centralEmbedL s f)=ᵐ[volume]
      (sourceClosedCollarBand centralThickness (2*centralThickness)).indicator
        (fun y => centralJetField f i (sourcePairCoordinates y)) := by
  have hr := lpRestrictionCLM_ae (sourceClosedCollarBand centralThickness (2*centralThickness))
    (centralPhysicalWholeCLM (centralSmoothJet f i))
  have he := hr.trans (ae_restrict_of_ae (centralPhysicalWholeCLM_smooth_ae f i))
  have hb : (lpRestrictionCLM (sourceClosedCollarBand centralThickness (2*centralThickness))
      (centralPhysicalWholeCLM (centralSmoothJet f i)))=ᵐ[volume.restrict
      (sourceClosedCollarBand centralThickness (2*centralThickness))]
      (fun y => centralJetField f i (sourcePairCoordinates y)) := by
    filter_upwards [he,ae_restrict_mem parentBand_measurable] with y hy hb
    rw [hy,indicator_of_mem (show y∈centralPhysical from parentBand_central hb)]
  exact lpZeroExtensionCLM_ae_of_ae parentBand_measurable _ hb

lemma central_parent_trace_eq (s : Fin 3 → ℝ) (f : centralSmoothFunctions) :
    smoothCollarTrace s centralThickness ((central_smooth f).comp sourcePairCLE.contDiff)=
      centralSmoothTrace s f 0 := by
  apply spectralTraceGraph_fst_injective (torusRate s)
  change (smoothCollarTrace s centralThickness ((central_smooth f).comp sourcePairCLE.contDiff)).val 0 =
    (centralSmoothTrace s f 0).val 0
  rw [centralSmoothTrace_fst]
  ext h
  rw [smoothCollarTrace_fst, centralTraceFourier_apply]
  rfl

lemma central_parent_partial (f : centralSmoothFunctions) (i : Fin 3) (y : Fin 3 → ℝ) :
    centralJetField f i.succ (sourcePairCoordinates y)=
      fderiv ℝ (fun y => f (sourcePairCoordinates y)) y (Pi.single i 1) := by
  rw [centralJetField_succ]
  have he := (((central_smooth f).differentiable (by simp) _).hasFDerivAt.comp y sourcePairCLE.hasFDerivAt).fderiv
  change fderiv ℝ f (sourcePairCLE y) (centralDirection i) =
    fderiv ℝ (f ∘ sourcePairCLE) y (Pi.single i 1)
  rw [he]
  have hi : sourcePairCLE.toContinuousLinearMap (Pi.single i 1)=centralDirection i := by
    fin_cases i <;> rfl
  exact congrArg (fderiv ℝ f (sourcePairCoordinates y)) hi |>.symm

lemma parentEndBand_measurable : MeasurableSet (sourceClosedCollarBand 0 centralThickness) :=
  (isCompact_sourceClosedCollarBand (by norm_num) (by norm_num [centralThickness])).measurableSet

lemma parentEndTime_mem {a : ℝ} (ha : a<0) (t : ℝ) (ht : t∈Icc 0 centralThickness) :
    affineEndTime a centralThickness t∈Icc 0 (-a*centralThickness) := by
  have hδ : 0<centralThickness := by norm_num [centralThickness]
  dsimp [affineEndTime]
  constructor
  · exact mul_nonneg_of_nonpos_of_nonpos ha.le (sub_nonpos.mpr ht.2)
  · nlinarith [mul_nonpos_of_nonpos_of_nonneg ha.le ht.1]

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : ℝ} (ha : a<0)

def parentEndValueCLM : spectralTraceGraph (torusRate s) →L[ℝ]
    Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
  (lpZeroExtensionCLM parentEndBand_measurable).comp
    ((Complex.reCLM.compLpL 2 (volume.restrict (sourceClosedCollarBand 0 centralThickness))).comp
      (attachedEndFlatCLM s hs ha.ne (show 0≤-a*centralThickness by
        exact mul_nonneg (neg_nonneg.mpr ha.le) (by norm_num [centralThickness]))
        (by norm_num [centralThickness]) (by norm_num) (by norm_num [centralThickness])
        (parentEndTime_mem ha) 0))

def parentEndGradientCLM (i : Fin 3) : spectralTraceGraph (torusRate s) →L[ℝ]
    Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
  (lpZeroExtensionCLM parentEndBand_measurable).comp
    (attachedEndGradientCLM s hs ha.ne (show 0≤-a*centralThickness by
        exact mul_nonneg (neg_nonneg.mpr ha.le) (by norm_num [centralThickness]))
      (by norm_num [centralThickness]) (by norm_num [centralThickness])
      (by norm_num) (by norm_num [centralThickness]) (parentEndTime_mem ha) i)

lemma parentEndValueCLM_ae (f : spectralTraceGraph (torusRate s)) :
    parentEndValueCLM s hs ha f=ᵐ[volume]
      (sourceClosedCollarBand 0 centralThickness).indicator
        (fun y => (attachedEndPoissonField s f a centralThickness 0 y).re) := by
  apply lpZeroExtensionCLM_ae_of_ae parentEndBand_measurable
  have he := attachedEndFlatCLM_ae s hs f ha.ne
    (show 0≤-a*centralThickness by exact mul_nonneg (neg_nonneg.mpr ha.le) (by norm_num [centralThickness]))
    (show (0:ℝ)≤centralThickness by norm_num [centralThickness]) (by norm_num) (by norm_num [centralThickness])
    (parentEndTime_mem ha) 0
  apply (Complex.reCLM.coeFn_compLpL _).trans
  filter_upwards [he] with y hy
  exact congrArg Complex.re hy

lemma parentEndGradientCLM_ae (f : spectralTraceGraph (torusRate s)) (i : Fin 3) :
    parentEndGradientCLM s hs ha i f=ᵐ[volume]
      (sourceClosedCollarBand 0 centralThickness).indicator
        (fun y => fderiv ℝ (fun y => (attachedEndPoissonField s f a centralThickness 0 y).re) y (Pi.single i 1)) := by
  apply lpZeroExtensionCLM_ae_of_ae parentEndBand_measurable
  exact attachedEndGradientL_ae s hs ha.ne
    (show 0≤-a*centralThickness by exact mul_nonneg (neg_nonneg.mpr ha.le) (by norm_num [centralThickness]))
    (by norm_num [centralThickness]) (by norm_num [centralThickness])
    (by norm_num) (by norm_num [centralThickness]) (parentEndTime_mem ha) i f

def parentJoinedComponentCLM (i : Fin 4) : CentralAmbient s →L[ℝ]
    Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
  parentCentralComponentCLM s i+
    ((Fin.cases (parentEndValueCLM s hs ha) (parentEndGradientCLM s hs ha) :
      Fin 4 → spectralTraceGraph (torusRate s) →L[ℝ] Lp ℝ 2 (volume : Measure (Fin 3 → ℝ))) i).comp (centralAmbientT s 0)

end ScalarConductivity

end

end OAI
