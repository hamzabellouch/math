import Mathlib
import OAI.Analysis.Conductivity.Flux.PhysicalEndDifferential
import OAI.Analysis.Conductivity.Variational.PhysicalEndLocalLipschitz

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix

def endAxialAffine (a b : ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![a*(x 0-b),x 1,x 2]

def endAxialMatrix (a : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := diagonal ![a,1,1]

lemma endAxialAffine_contDiff (a b : ℝ) : ContDiff ℝ (↑(⊤:ℕ∞)) (endAxialAffine a b) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ _ (fun x : Fin 3 → ℝ => a*(x 0-b))
    fun_prop
  · change ContDiff ℝ _ (fun x : Fin 3 → ℝ => x 1)
    fun_prop
  · change ContDiff ℝ _ (fun x : Fin 3 → ℝ => x 2)
    fun_prop

lemma endAxialAffine_hasFDeriv (a b : ℝ) (x : Fin 3 → ℝ) :
    HasFDerivAt (endAxialAffine a b) (Matrix.toLin' (endAxialMatrix a)).toContinuousLinearMap x := by
  have hc (k : Fin 3) : HasFDerivAt (fun y => endAxialAffine a b y k)
      ((ContinuousLinearMap.proj k : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
        (Matrix.toLin' (endAxialMatrix a)).toContinuousLinearMap) x := by
    fin_cases k
    · convert! ((hasFDerivAt_apply (𝕜:=ℝ) (0:Fin 3) x).sub_const b).const_mul a using 1
      ext v
      simp [endAxialMatrix,Matrix.toLin'_apply,Matrix.mulVec_diagonal]
    · convert! hasFDerivAt_apply (𝕜:=ℝ) (1:Fin 3) x using 1
      ext v
      simp [endAxialMatrix,Matrix.toLin'_apply,Matrix.mulVec_diagonal]
    · convert! hasFDerivAt_apply (𝕜:=ℝ) (2:Fin 3) x using 1
      ext v
      simp [endAxialMatrix,Matrix.toLin'_apply,Matrix.mulVec_diagonal]
  convert! hasFDerivAt_pi.mpr hc using 1

lemma torusAngles_endAxialAffine (a b : ℝ) (x : Fin 3 → ℝ) :
    torusAngles (endAxialAffine a b x)=torusAngles x := by
  ext k
  fin_cases k <;> rfl

def attachedEndPoissonField (s : Fin 3 → ℝ) (f : spectralTraceGraph (torusRate s))
    (a b : ℝ) (j : Fin 4) (y : Fin 3 → ℝ) : ℂ :=
  endPoissonField s f j (a*(sourceCollarTime y-b),sourcePhysicalAngles y)

lemma measurable_attachedEndPoissonField (s : Fin 3 → ℝ)
    (f : spectralTraceGraph (torusRate s)) (a b : ℝ) (j : Fin 4) :
    Measurable (attachedEndPoissonField s f a b j) := by
  apply (measurable_endPoissonField s f j).comp
  exact (measurable_const.mul (measurable_sourcePhysicalCoordinates.fst.sub measurable_const)).prodMk
    measurable_sourcePhysicalAngles

lemma attachedEndPoissonField_angular (s : Fin 3 → ℝ)
    (f : spectralTraceGraph (torusRate s)) (a b : ℝ) (j : Fin 4)
    {t : ℝ} (ht : t∈Icc (-(1:ℝ)/100) (1/100)) (θ : UnitAddTorus (Fin 2)) :
    attachedEndPoissonField s f a b j (sourceAngularCollar t θ)=
      endPoissonField s f j (a*(t-b),θ) := by
  simp only [attachedEndPoissonField,sourceAngular_time ht,sourcePhysicalAngles_angular ht]

lemma attachedEndPoissonField_piece (s : Fin 3 → ℝ)
    (f : spectralTraceGraph (torusRate s)) (a b : ℝ) (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) :
    attachedEndPoissonField s f a b 0 (sourceCollarPiece i j x)=
      endFlatPoisson s f (endAxialAffine a b (sourceFaceAngles i j x)) := by
  obtain ⟨ht,ha,hb⟩ := mem_sourceExtendedBox.mp hx
  rw [←sourceFaceAngles_physical i j ha hb,attachedEndPoissonField_angular s f a b 0 ht,
    endFlatPoisson_eq,torusAngles_endAxialAffine]
  rfl

lemma attachedEndPoissonField_local_eq (s : Fin 3 → ℝ)
    (f : spectralTraceGraph (torusRate s)) (a b : ℝ) (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) :
    attachedEndPoissonField s f a b 0 =ᶠ[𝓝 (sourceCollarPiece i j x)]
      (fun y => endFlatPoisson s f (endAxialAffine a b (sourceFaceAngles i j (sourceCollarInverse i j y)))) := by
  change ∀ᶠ y in 𝓝 (sourceCollarPiece i j x),attachedEndPoissonField s f a b 0 y=
    endFlatPoisson s f (endAxialAffine a b (sourceFaceAngles i j (sourceCollarInverse i j y)))
  rw [←sourceCollarPiece_map_nhds i j hx,Filter.eventually_map]
  filter_upwards [isOpen_sourceCollarOpenBox.mem_nhds hx,
    sourceCollarInverse_eventually_left i j hx] with y hy hi
  rw [hi]
  exact attachedEndPoissonField_piece s f a b i j (sourceCollarOpenBox_subset hy)

theorem attachedEndPoissonField_hasFDeriv (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (a b : ℝ) (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) (ht : 0<a*(x 0-b)) :
    HasFDerivAt (attachedEndPoissonField s f a b 0)
      ((fderiv ℝ (endFlatPoisson s f) (endAxialAffine a b (sourceFaceAngles i j x))).comp
        (((Matrix.toLin' (endAxialMatrix a)).toContinuousLinearMap).comp
          (((Matrix.toLin' (sourceFaceAngleMatrix i j x)).toContinuousLinearMap).comp
            (sourceCollarTangentEquiv i j x (sourceCollarOpenBox_subset hx)).symm.toContinuousLinearMap)))
      (sourceCollarPiece i j x) := by
  have he := sourceCollarInverse_point i j hx
  have h1 := (sourceCollarInverse_hasStrictFDeriv i j hx).hasFDerivAt
  have h2 := (sourceFaceAngles_hasFDeriv i j (sourceCollarInverse i j (sourceCollarPiece i j x))).comp
    (sourceCollarPiece i j x) h1
  rw [he] at h2
  have h3a : HasFDerivAt (endAxialAffine a b)
      (Matrix.toLin' (endAxialMatrix a)).toContinuousLinearMap
      (sourceFaceAngles i j (sourceCollarInverse i j (sourceCollarPiece i j x))) := by
    simpa only [he] using endAxialAffine_hasFDeriv a b (sourceFaceAngles i j x)
  have h3 := h3a.comp (sourceCollarPiece i j x) h2
  have hd := (endFlatPoisson_hasFDeriv s hs f (x:=endAxialAffine a b (sourceFaceAngles i j x)) ht).differentiableAt.hasFDerivAt
  have hda : HasFDerivAt (endFlatPoisson s f)
      (fderiv ℝ (endFlatPoisson s f) (endAxialAffine a b (sourceFaceAngles i j x)))
      (endAxialAffine a b (sourceFaceAngles i j (sourceCollarInverse i j (sourceCollarPiece i j x)))) := by
    simpa only [he] using hd
  have h3' := hda.comp (sourceCollarPiece i j x) h3
  exact h3'.congr_of_eventuallyEq (attachedEndPoissonField_local_eq s f a b i j hx)

lemma attachedEndPoissonField_eq_continuation (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (a b : ℝ) {y : Fin 3 → ℝ}
    (hy : 0<a*(sourceCollarTime y-b)) {x : Fin 3 → ℝ}
    (hx : x 0=a*(sourceCollarTime y-b)) (hθ : torusAngles x=sourcePhysicalAngles y) :
    (attachedEndPoissonField s f a b 0 y).re=
      torusRealContinuation s ((mFourierBasis (d:=Fin 2)).repr.symm (f.val 0)) x := by
  unfold torusRealContinuation
  rw [hx,hθ,torusPoissonContinuous_apply hs hy]
  unfold attachedEndPoissonField endPoissonField
  apply congrArg Complex.re
  apply tsum_congr
  intro h
  have hc : mFourierCoeff (((mFourierBasis (d:=Fin 2)).repr.symm (f.val 0)):TorusL2) h=f.val 0 h := by
    rw [←mFourierBasis_repr,LinearIsometryEquiv.apply_symm_apply]
  simp only [endPoissonModeField,endModeCoefficient,hc,Matrix.cons_val_zero]

theorem attachedEndPoissonField_localLip (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (a b : ℝ) {x : Fin 3 → ℝ}
    (ht : 0<a*(sourceCollarTime x-b)) (hx : ∀ i,sourceComplexDirections x i≠0) :
    LocalLipAt (fun y => (attachedEndPoissonField s f a b 0 y).re) x := by
  have hflat := (localLipAt_of_contDiffAt ((endAxialAffine_contDiff a b).of_le
    (show (1:WithTop ℕ∞)≤↑(⊤:ℕ∞) by simp)).contDiffAt).comp (sourceLocalFlat_localLip hx)
  have hc := (torusRealContinuation_smooth hs ((mFourierBasis (d:=Fin 2)).repr.symm (f.val 0))).of_le
    (show (1:WithTop ℕ∞)≤↑(⊤:ℕ∞) by simp)
  have hc' := hc.contDiffAt ((axial_halfspace_open 0).mem_nhds
    (show 0<(endAxialAffine a b (sourceLocalFlat x x)) 0 from ht))
  apply ((localLipAt_of_contDiffAt hc').comp (f:=endAxialAffine a b ∘ sourceLocalFlat x) hflat).congr
  have htime : ∀ᶠ y in 𝓝 x,0<a*(sourceCollarTime y-b) :=
    (continuous_const.mul (locallyLipschitz_sourceCollarTime.continuous.sub continuous_const)).continuousAt
      (Ioi_mem_nhds ht)
  have hdirs : ∀ᶠ y in 𝓝 x,∀ i,sourceComplexDirections y i≠0 := by
    rw [eventually_all]
    intro i
    exact (locallyLipschitz_sourceDirection i).continuous.continuousAt (isOpen_ne.mem_nhds (hx i))
  filter_upwards [htime,hdirs] with y hyt hyd
  exact (attachedEndPoissonField_eq_continuation s hs f a b hyt rfl
    ((torusAngles_endAxialAffine a b _).trans (sourceLocalFlat_angles hx hyd))).symm

end ScalarConductivity

end

end OAI
