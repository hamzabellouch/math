import Mathlib
import OAI.Analysis.Conductivity.Sobolev.ParentCompletionJoin

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def actualChildSign (k : Fin 2) : ℝ := if k=0 then 1 else -1

def childAxis (i : Fin 3) : Fin 3 := ![1,0,2] i

lemma childBand_central (k : Fin 2) {y : Fin 3 → ℝ}
    (hy : y∈sourceClosedCollarBand (-2*centralThickness) (-centralThickness)) :
    sourcePairCoordinates (sourceChildCoordinates (actualChildSign k) y)∈centralClosed := by
  rw [sourceClosedCollarBand_eq _ _ (by norm_num [centralThickness])
    (by norm_num [centralThickness])] at hy
  rcases mem_iUnion.mp hy with ⟨i,hi⟩
  rcases mem_iUnion.mp hi with ⟨j,hj⟩
  rcases hj with ⟨x,hx,rfl⟩
  exact sourceChildCollar_central i j (by fin_cases k <;> simp [actualChildSign]) hx

lemma childCentralBand_measurable :
    MeasurableSet (sourceClosedCollarBand (-2*centralThickness) (-centralThickness)) :=
  (isCompact_sourceClosedCollarBand (by norm_num [centralThickness]) (by norm_num [centralThickness])).measurableSet

def childCentralRawComponentCLM (s : Fin 3 → ℝ) (k : Fin 2) (i : Fin 4) :
    CentralAmbient s →L[ℝ] Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
  (lpZeroExtensionCLM childCentralBand_measurable).comp
    ((lpRestrictionCLM (sourceClosedCollarBand (-2*centralThickness) (-centralThickness))).comp
      ((sourceChildPullbackCLM (actualChildSign k)).comp
        (centralPhysicalWholeCLM.comp (centralAmbientComponent s i))))

lemma childCentralRawComponentCLM_smooth_ae (s : Fin 3 → ℝ) (k : Fin 2)
    (f : centralSmoothFunctions) (i : Fin 4) :
    childCentralRawComponentCLM s k i (centralEmbedL s f)=ᵐ[volume]
      (sourceClosedCollarBand (-2*centralThickness) (-centralThickness)).indicator
        (fun y => centralJetField f i (sourcePairCoordinates (sourceChildCoordinates (actualChildSign k) y))) := by
  have hp := (sourceChildPullbackCLM_ae (actualChildSign k) (centralPhysicalWholeCLM (centralSmoothJet f i))).trans
    ((sourceChildCoordinates_quasi (actualChildSign k)).ae_eq_comp (centralPhysicalWholeCLM_smooth_ae f i))
  have hr := (lpRestrictionCLM_ae (sourceClosedCollarBand (-2*centralThickness) (-centralThickness))
    (sourceChildPullbackCLM (actualChildSign k) (centralPhysicalWholeCLM (centralSmoothJet f i)))).trans
      (ae_restrict_of_ae hp)
  apply lpZeroExtensionCLM_ae_of_ae childCentralBand_measurable
  filter_upwards [hr,ae_restrict_mem childCentralBand_measurable] with y hy hb
  change (lpRestrictionCLM (sourceClosedCollarBand (-2*centralThickness) (-centralThickness))
    (sourceChildPullbackCLM (actualChildSign k) (centralPhysicalWholeCLM (centralSmoothJet f i)))) y=_
  rw [hy,Function.comp_apply,indicator_of_mem (show sourceChildCoordinates (actualChildSign k) y∈centralPhysical from childBand_central k hb)]

lemma central_child_partial (k : Fin 2) (f : centralSmoothFunctions) (i : Fin 3) (y : Fin 3 → ℝ) :
    sourceScale*centralJetField f (childAxis i).succ
      (sourcePairCoordinates (sourceChildCoordinates (actualChildSign k) y))=
        fderiv ℝ (fun y => f (sourcePairCoordinates (sourceChildCoordinates (actualChildSign k) y))) y (Pi.single i 1) := by
  have he := (((central_smooth f).comp sourcePairCLE.contDiff).differentiable (by simp)
    (sourceChildCoordinates (actualChildSign k) y)).hasFDerivAt.comp y (sourceChildCoordinates_hasFDeriv (actualChildSign k) y)
  have hi : sourceChildDerivative (Pi.single i 1)=sourceScale • Pi.single (childAxis i) 1 := by
    rw [sourceChildDerivative_apply]
    fin_cases i <;> ext j <;> fin_cases j <;> norm_num [childAxis,Pi.single_apply,Fin.ext_iff]
  rw [central_parent_partial]
  change sourceScale*(fderiv ℝ (f ∘ sourcePairCLE) (sourceChildCoordinates (actualChildSign k) y)) (Pi.single (childAxis i) 1)=
    fderiv ℝ ((f ∘ sourcePairCLE) ∘ sourceChildCoordinates (actualChildSign k)) y (Pi.single i 1)
  rw [he.fderiv,ContinuousLinearMap.comp_apply,hi,map_smul,smul_eq_mul]

lemma central_child_trace_eq (s : Fin 3 → ℝ) (k : Fin 2) (f : centralSmoothFunctions) :
    smoothCollarTrace s (-centralThickness)
      (((central_smooth f).comp sourcePairCLE.contDiff).comp (sourceChildCoordinates_contDiff (actualChildSign k)))=
        centralSmoothTrace s f k.succ := by
  apply spectralTraceGraph_fst_injective (torusRate s)
  change (smoothCollarTrace s (-centralThickness)
    (((central_smooth f).comp sourcePairCLE.contDiff).comp (sourceChildCoordinates_contDiff (actualChildSign k)))).val 0 =
      (centralSmoothTrace s f k.succ).val 0
  rw [centralSmoothTrace_fst]
  ext h
  rw [smoothCollarTrace_fst,centralTraceFourier_apply]
  fin_cases k <;> rfl

def childCentralComponentCLM (s : Fin 3 → ℝ) (k : Fin 2) (i : Fin 4) :
    CentralAmbient s →L[ℝ] Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
  Fin.cases (childCentralRawComponentCLM s k 0)
    (fun j => sourceScale • childCentralRawComponentCLM s k (childAxis j).succ) i

lemma childCentralComponentCLM_smooth_value (s : Fin 3 → ℝ) (k : Fin 2) (f : centralSmoothFunctions) :
    childCentralComponentCLM s k 0 (centralEmbedL s f)=ᵐ[volume]
      (sourceClosedCollarBand (-2*centralThickness) (-centralThickness)).indicator
        (fun y => f (sourcePairCoordinates (sourceChildCoordinates (actualChildSign k) y))) :=
  childCentralRawComponentCLM_smooth_ae s k f 0

lemma childCentralComponentCLM_smooth_gradient (s : Fin 3 → ℝ) (k : Fin 2)
    (f : centralSmoothFunctions) (i : Fin 3) :
    childCentralComponentCLM s k i.succ (centralEmbedL s f)=ᵐ[volume]
      (sourceClosedCollarBand (-2*centralThickness) (-centralThickness)).indicator
        (fun y => fderiv ℝ (fun y => f (sourcePairCoordinates (sourceChildCoordinates (actualChildSign k) y))) y (Pi.single i 1)) := by
  apply (Lp.coeFn_smul sourceScale (childCentralRawComponentCLM s k (childAxis i).succ (centralEmbedL s f))).trans
  filter_upwards [childCentralRawComponentCLM_smooth_ae s k f (childAxis i).succ] with y hy
  change sourceScale*_=_
  rw [hy]
  by_cases hb : y∈sourceClosedCollarBand (-2*centralThickness) (-centralThickness)
  · simp only [indicator_of_mem hb,central_child_partial]
  · simp only [indicator_of_notMem hb,mul_zero]

lemma childEndBand_measurable : MeasurableSet (sourceClosedCollarBand (-centralThickness) 0) :=
  (isCompact_sourceClosedCollarBand (by norm_num [centralThickness]) (by norm_num [centralThickness])).measurableSet

lemma childEndTime_mem {a : ℝ} (ha : 0<a) (t : ℝ) (ht : t∈Icc (-centralThickness) 0) :
    affineEndTime a (-centralThickness) t∈Icc 0 (a*centralThickness) := by
  dsimp [affineEndTime]
  constructor
  · exact mul_nonneg ha.le (sub_nonneg.mpr ht.1)
  · nlinarith [mul_nonpos_of_nonneg_of_nonpos ha.le ht.2]

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : ℝ} (ha : 0<a)

def childEndValueCLM : spectralTraceGraph (torusRate s) →L[ℝ]
    Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
  (lpZeroExtensionCLM childEndBand_measurable).comp
    ((Complex.reCLM.compLpL 2 (volume.restrict (sourceClosedCollarBand (-centralThickness) 0))).comp
      (attachedEndFlatCLM s hs ha.ne' (show 0≤a*centralThickness by
        exact mul_nonneg ha.le (by norm_num [centralThickness]))
        (by norm_num [centralThickness]) (by norm_num [centralThickness]) (by norm_num)
        (childEndTime_mem ha) 0))

def childEndGradientCLM (i : Fin 3) : spectralTraceGraph (torusRate s) →L[ℝ]
    Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
  (lpZeroExtensionCLM childEndBand_measurable).comp
    (attachedEndGradientCLM s hs ha.ne' (show 0≤a*centralThickness by
        exact mul_nonneg ha.le (by norm_num [centralThickness]))
      (by norm_num [centralThickness]) (by norm_num [centralThickness])
      (by norm_num [centralThickness]) (by norm_num) (childEndTime_mem ha) i)

lemma childEndValueCLM_ae (f : spectralTraceGraph (torusRate s)) :
    childEndValueCLM s hs ha f=ᵐ[volume]
      (sourceClosedCollarBand (-centralThickness) 0).indicator
        (fun y => (attachedEndPoissonField s f a (-centralThickness) 0 y).re) := by
  apply lpZeroExtensionCLM_ae_of_ae childEndBand_measurable
  have he := attachedEndFlatCLM_ae s hs f ha.ne'
    (show 0≤a*centralThickness by exact mul_nonneg ha.le (by norm_num [centralThickness]))
    (show -centralThickness≤(0:ℝ) by norm_num [centralThickness]) (by norm_num [centralThickness]) (by norm_num)
    (childEndTime_mem ha) 0
  apply (Complex.reCLM.coeFn_compLpL _).trans
  filter_upwards [he] with y hy
  exact congrArg Complex.re hy

lemma childEndGradientCLM_ae (f : spectralTraceGraph (torusRate s)) (i : Fin 3) :
    childEndGradientCLM s hs ha i f=ᵐ[volume]
      (sourceClosedCollarBand (-centralThickness) 0).indicator
        (fun y => fderiv ℝ (fun y => (attachedEndPoissonField s f a (-centralThickness) 0 y).re) y (Pi.single i 1)) := by
  apply lpZeroExtensionCLM_ae_of_ae childEndBand_measurable
  exact attachedEndGradientL_ae s hs ha.ne'
    (show 0≤a*centralThickness by exact mul_nonneg ha.le (by norm_num [centralThickness]))
    (by norm_num [centralThickness]) (by norm_num [centralThickness])
    (by norm_num [centralThickness]) (by norm_num) (childEndTime_mem ha) i f

def childJoinedComponentCLM (k : Fin 2) (i : Fin 4) : CentralAmbient s →L[ℝ]
    Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
  childCentralComponentCLM s k i+
    ((Fin.cases (childEndValueCLM s hs ha) (childEndGradientCLM s hs ha) :
      Fin 4 → spectralTraceGraph (torusRate s) →L[ℝ] Lp ℝ 2 (volume : Measure (Fin 3 → ℝ))) i).comp (centralAmbientT s k.succ)

end ScalarConductivity

end

end OAI
