import Mathlib
import OAI.Analysis.Conductivity.Sobolev.LocalJoinedH1
import OAI.Analysis.Conductivity.Sobolev.LpFourJet
import OAI.Analysis.Conductivity.Branching.ParentCentralL2

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology

lemma parent_band_indicator_join {a : ℝ} (ha : a<0) (y : Fin 3 → ℝ)
    (hy : y∈sourceClosedCollarBand 0 (2*centralThickness))
    (hne : sourceCollarTime y≠centralThickness) (q p : (Fin 3 → ℝ) → ℝ) :
    (sourceClosedCollarBand centralThickness (2*centralThickness)).indicator q y+
      (sourceClosedCollarBand 0 centralThickness).indicator p y=
        if 0<a*(sourceCollarTime y-centralThickness) then p y else q y := by
  rcases lt_or_gt_of_ne hne with ht | ht
  · have hp : 0<a*(sourceCollarTime y-centralThickness) :=
      mul_pos_of_neg_of_neg ha (sub_neg.mpr ht)
    have hc : y∉sourceClosedCollarBand centralThickness (2*centralThickness) := fun h => not_le_of_gt ht h.1
    have he : y∈sourceClosedCollarBand 0 centralThickness := ⟨hy.1,ht.le⟩
    simp [hc,he,hp]
  · have hp : ¬0<a*(sourceCollarTime y-centralThickness) :=
      not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg ha.le (sub_nonneg.mpr ht.le))
    have hc : y∈sourceClosedCollarBand centralThickness (2*centralThickness) := ⟨ht.le,hy.2⟩
    have he : y∉sourceClosedCollarBand 0 centralThickness := fun h => not_le_of_gt ht h.2
    simp [hc,he,hp]

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : ℝ} (ha : a<0)
  {χ : (Fin 3 → ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)

def parentLocalComponentCLM (i : Fin 4) : CentralAmbient s →L[ℝ]
    Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
  Fin.cases ((compactMultiplierCLM hχ.continuous hc).comp (parentJoinedComponentCLM s hs ha 0))
    (fun j => ((compactMultiplierCLM ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
        (hc.fderiv_apply ℝ (Pi.single j 1))).comp (parentJoinedComponentCLM s hs ha 0))+
      ((compactMultiplierCLM hχ.continuous hc).comp (parentJoinedComponentCLM s hs ha j.succ))) i

def physicalFourJetCLM : (Fin 4 → Lp ℝ 2 (volume : Measure (Fin 3 → ℝ))) →L[ℝ] JetSpace :=
  (lpRestrictionCLM ball).comp
    (((Lp.compMeasurePreservingₗᵢ ℝ ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toHomeomorph.toMeasurableEquiv)
      (PiLp.volume_preserving_ofLp (Fin 3))).toContinuousLinearMap).comp (lpFourJetCLM volume))

lemma physicalFourJetCLM_ae (f : Fin 4 → Lp ℝ 2 (volume : Measure (Fin 3 → ℝ))) :
    physicalFourJetCLM f=ᵐ[ballMeasure] (fun x => WithLp.toLp 2 (fun i => f i (WithLp.ofLp x))) := by
  apply (lpRestrictionCLM_ae ball _).trans
  apply ae_restrict_of_ae
  apply (Lp.coeFn_compMeasurePreserving _ (PiLp.volume_preserving_ofLp (Fin 3))).trans
  exact (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp (lpFourJetCLM_ae volume f)

def parentLocalJetCLM : CentralAmbient s →L[ℝ] JetSpace :=
  physicalFourJetCLM.comp (ContinuousLinearMap.pi (parentLocalComponentCLM s hs ha hχ hc))

end

open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : ℝ} (ha : a<0)
  {χ : (Fin 3 → ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)
  (hχs : tsupport χ⊆sourceClosedCollarBand 0 (2*centralThickness))

lemma parentJoinedComponentCLM_smooth_value (f : centralSmoothFunctions) :
    parentJoinedComponentCLM s hs ha 0 (centralEmbedL s f)=ᵐ[volume] (fun y =>
      (sourceClosedCollarBand centralThickness (2*centralThickness)).indicator
        (fun y => f (sourcePairCoordinates y)) y+
      (sourceClosedCollarBand 0 centralThickness).indicator
        (fun y => (attachedEndPoissonField s (centralSmoothTrace s f 0) a centralThickness 0 y).re) y) := by
  apply (Lp.coeFn_add _ _).trans
  filter_upwards [parentCentralComponentCLM_smooth_ae s f 0,parentEndValueCLM_ae s hs ha (centralSmoothTrace s f 0)] with y hy hz
  change (parentCentralComponentCLM s 0 (centralEmbedL s f)) y+
    (parentEndValueCLM s hs ha (centralSmoothTrace s f 0)) y=_
  rw [hy,hz]
  rfl

lemma parentJoinedComponentCLM_smooth_gradient (f : centralSmoothFunctions) (i : Fin 3) :
    parentJoinedComponentCLM s hs ha i.succ (centralEmbedL s f)=ᵐ[volume] (fun y =>
      (sourceClosedCollarBand centralThickness (2*centralThickness)).indicator
        (fun y => fderiv ℝ (fun y => f (sourcePairCoordinates y)) y (Pi.single i 1)) y+
      (sourceClosedCollarBand 0 centralThickness).indicator
        (fun y => fderiv ℝ (fun y => (attachedEndPoissonField s (centralSmoothTrace s f 0) a centralThickness 0 y).re) y (Pi.single i 1)) y) := by
  apply (Lp.coeFn_add _ _).trans
  filter_upwards [parentCentralComponentCLM_smooth_ae s f i.succ,parentEndGradientCLM_ae s hs ha (centralSmoothTrace s f 0) i] with y hy hz
  change (parentCentralComponentCLM s i.succ (centralEmbedL s f)) y+
    (parentEndGradientCLM s hs ha i (centralSmoothTrace s f 0)) y=_
  rw [hy,hz]
  simp only [central_parent_partial]

include hχs in
lemma parentLocalComponentCLM_smooth_value (f : centralSmoothFunctions) :
    parentLocalComponentCLM s hs ha hχ hc 0 (centralEmbedL s f)=ᵐ[volume]
      localJoinedValue (fun y => a*(sourceCollarTime y-centralThickness)) χ
        (fun y => f (sourcePairCoordinates y))
        (fun y => (attachedEndPoissonField s (centralSmoothTrace s f 0) a centralThickness 0 y).re) := by
  have he := compactMultiplierCLM_ae hχ.continuous hc (parentJoinedComponentCLM s hs ha 0 (centralEmbedL s f))
  filter_upwards [he,parentJoinedComponentCLM_smooth_value s hs ha f,
    sourceColevel_ae_ne (show centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])] with y hy hv hn
  simp only [parentLocalComponentCLM, Fin.cases_zero, ContinuousLinearMap.comp_apply, localJoinedValue]
  rw [hy,hv]
  by_cases hys : y∈tsupport χ
  · rw [parent_band_indicator_join ha y (hχs hys) hn]
  · rw [image_eq_zero_of_notMem_tsupport hys]
    simp

include hχs in
lemma parentLocalComponentCLM_smooth_gradient (f : centralSmoothFunctions) (i : Fin 3) :
    parentLocalComponentCLM s hs ha hχ hc i.succ (centralEmbedL s f)=ᵐ[volume]
      localJoinedGradient (fun y => a*(sourceCollarTime y-centralThickness)) χ
        (fun y => f (sourcePairCoordinates y))
        (fun y => (attachedEndPoissonField s (centralSmoothTrace s f 0) a centralThickness 0 y).re) i := by
  have he₀ := compactMultiplierCLM_ae ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hc.fderiv_apply ℝ (Pi.single i 1)) (parentJoinedComponentCLM s hs ha 0 (centralEmbedL s f))
  have he₁ := compactMultiplierCLM_ae hχ.continuous hc (parentJoinedComponentCLM s hs ha i.succ (centralEmbedL s f))
  apply (Lp.coeFn_add _ _).trans
  filter_upwards [he₀,he₁,parentJoinedComponentCLM_smooth_value s hs ha f,
    parentJoinedComponentCLM_smooth_gradient s hs ha f i,
    sourceColevel_ae_ne (show centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])] with y h₀ h₁ hv hg hn
  change (compactMultiplierCLM ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hc.fderiv_apply ℝ (Pi.single i 1)) (parentJoinedComponentCLM s hs ha 0 (centralEmbedL s f))) y+
      (compactMultiplierCLM hχ.continuous hc (parentJoinedComponentCLM s hs ha i.succ (centralEmbedL s f))) y=_
  rw [h₀,h₁,hv,hg]
  simp only [localJoinedGradient]
  by_cases hys : y∈tsupport χ
  · rw [parent_band_indicator_join ha y (hχs hys) hn,
      parent_band_indicator_join ha y (hχs hys) hn]
  · rw [image_eq_zero_of_notMem_tsupport hys,fderiv_of_notMem_tsupport ℝ hys]
    simp

include hχs in
lemma parentLocalJetCLM_smooth_ae (f : centralSmoothFunctions) :
    parentLocalJetCLM s hs ha hχ hc (centralEmbedL s f)=ᵐ[ballMeasure] (fun x =>
      WithLp.toLp 2 (Fin.cases
        (localJoinedValue (fun y => a*(sourceCollarTime y-centralThickness)) χ
          (fun y => f (sourcePairCoordinates y))
          (fun y => (attachedEndPoissonField s (centralSmoothTrace s f 0) a centralThickness 0 y).re) (WithLp.ofLp x))
        (fun i => localJoinedGradient (fun y => a*(sourceCollarTime y-centralThickness)) χ
          (fun y => f (sourcePairCoordinates y))
          (fun y => (attachedEndPoissonField s (centralSmoothTrace s f 0) a centralThickness 0 y).re) i (WithLp.ofLp x)))) := by
  have h₀ := ae_restrict_of_ae (s:=ball) ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp
    (parentLocalComponentCLM_smooth_value s hs ha hχ hc hχs f))
  have h₁ (i : Fin 3) := ae_restrict_of_ae (s:=ball) ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp
    (parentLocalComponentCLM_smooth_gradient s hs ha hχ hc hχs f i))
  apply (physicalFourJetCLM_ae (fun i => parentLocalComponentCLM s hs ha hχ hc i (centralEmbedL s f))).trans
  filter_upwards [h₀,ae_all_iff.mpr h₁] with x hv hg
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hv
  · exact hg j

end ScalarConductivity

end

end OAI
