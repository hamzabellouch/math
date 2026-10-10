import Mathlib
import OAI.Analysis.Conductivity.Branching.ChildCentralL2

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology

lemma child_band_indicator_join {a : ℝ} (ha : 0<a) (y : Fin 3 → ℝ)
    (hy : y∈sourceClosedCollarBand (-2*centralThickness) 0)
    (hne : sourceCollarTime y≠-centralThickness) (q p : (Fin 3 → ℝ) → ℝ) :
    (sourceClosedCollarBand (-2*centralThickness) (-centralThickness)).indicator q y+
      (sourceClosedCollarBand (-centralThickness) 0).indicator p y=
        if 0<a*(sourceCollarTime y-(-centralThickness)) then p y else q y := by
  rcases lt_or_gt_of_ne hne with ht | ht
  · have hp : ¬0<a*(sourceCollarTime y-(-centralThickness)) :=
      not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos ha.le (sub_nonpos.mpr ht.le))
    have hc : y∈sourceClosedCollarBand (-2*centralThickness) (-centralThickness) := ⟨hy.1,ht.le⟩
    have he : y∉sourceClosedCollarBand (-centralThickness) 0 := fun h => not_le_of_gt ht h.1
    simp only [indicator_of_mem hc,indicator_of_notMem he,add_zero,ite_eq_right hp]
  · have hp : 0<a*(sourceCollarTime y-(-centralThickness)) := mul_pos ha (sub_pos.mpr ht)
    have hc : y∉sourceClosedCollarBand (-2*centralThickness) (-centralThickness) := fun h => not_le_of_gt ht h.2
    have he : y∈sourceClosedCollarBand (-centralThickness) 0 := ⟨ht.le,hy.2⟩
    simp only [indicator_of_notMem hc,indicator_of_mem he,zero_add,ite_eq_left hp]

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : ℝ} (ha : 0<a)
  (k : Fin 2)
  {χ : (Fin 3 → ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)

def childLocalComponentCLM (i : Fin 4) : CentralAmbient s →L[ℝ]
    Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
  Fin.cases ((compactMultiplierCLM hχ.continuous hc).comp (childJoinedComponentCLM s hs ha k 0))
    (fun j => ((compactMultiplierCLM ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
        (hc.fderiv_apply ℝ (Pi.single j 1))).comp (childJoinedComponentCLM s hs ha k 0))+
      ((compactMultiplierCLM hχ.continuous hc).comp (childJoinedComponentCLM s hs ha k j.succ))) i

def childLocalJetCLM : CentralAmbient s →L[ℝ] JetSpace :=
  physicalFourJetCLM.comp (ContinuousLinearMap.pi (childLocalComponentCLM s hs ha k hχ hc))

end

open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : ℝ} (ha : 0<a)
  (k : Fin 2)
  {χ : (Fin 3 → ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)
  (hχs : tsupport χ⊆sourceClosedCollarBand (-2*centralThickness) 0)

lemma childJoinedComponentCLM_smooth_value (f : centralSmoothFunctions) :
    childJoinedComponentCLM s hs ha k 0 (centralEmbedL s f)=ᵐ[volume] (fun y =>
      (sourceClosedCollarBand (-2*centralThickness) (-centralThickness)).indicator
        (fun y => f (sourcePairCoordinates (sourceChildCoordinates (actualChildSign k) y))) y+
      (sourceClosedCollarBand (-centralThickness) 0).indicator
        (fun y => (attachedEndPoissonField s (centralSmoothTrace s f k.succ) a (-centralThickness) 0 y).re) y) := by
  apply (Lp.coeFn_add _ _).trans
  filter_upwards [childCentralComponentCLM_smooth_value s k f,childEndValueCLM_ae s hs ha (centralSmoothTrace s f k.succ)] with y hy hz
  change (childCentralComponentCLM s k 0 (centralEmbedL s f)) y+
    (childEndValueCLM s hs ha (centralSmoothTrace s f k.succ)) y=_
  rw [hy,hz]

lemma childJoinedComponentCLM_smooth_gradient (f : centralSmoothFunctions) (i : Fin 3) :
    childJoinedComponentCLM s hs ha k i.succ (centralEmbedL s f)=ᵐ[volume] (fun y =>
      (sourceClosedCollarBand (-2*centralThickness) (-centralThickness)).indicator
        (fun y => fderiv ℝ (fun y => f (sourcePairCoordinates (sourceChildCoordinates (actualChildSign k) y))) y (Pi.single i 1)) y+
      (sourceClosedCollarBand (-centralThickness) 0).indicator
        (fun y => fderiv ℝ (fun y => (attachedEndPoissonField s (centralSmoothTrace s f k.succ) a (-centralThickness) 0 y).re) y (Pi.single i 1)) y) := by
  apply (Lp.coeFn_add _ _).trans
  filter_upwards [childCentralComponentCLM_smooth_gradient s k f i,childEndGradientCLM_ae s hs ha (centralSmoothTrace s f k.succ) i] with y hy hz
  change (childCentralComponentCLM s k i.succ (centralEmbedL s f)) y+
    (childEndGradientCLM s hs ha i (centralSmoothTrace s f k.succ)) y=_
  rw [hy,hz]

include hχs in
lemma childLocalComponentCLM_smooth_value (f : centralSmoothFunctions) :
    childLocalComponentCLM s hs ha k hχ hc 0 (centralEmbedL s f)=ᵐ[volume]
      localJoinedValue (fun y => a*(sourceCollarTime y-(-centralThickness))) χ
        (fun y => f (sourcePairCoordinates (sourceChildCoordinates (actualChildSign k) y)))
        (fun y => (attachedEndPoissonField s (centralSmoothTrace s f k.succ) a (-centralThickness) 0 y).re) := by
  have he := compactMultiplierCLM_ae hχ.continuous hc (childJoinedComponentCLM s hs ha k 0 (centralEmbedL s f))
  filter_upwards [he,childJoinedComponentCLM_smooth_value s hs ha k f,
    sourceColevel_ae_ne (show -centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])] with y hy hv hn
  simp only [childLocalComponentCLM, Fin.cases_zero, ContinuousLinearMap.comp_apply, localJoinedValue]
  rw [hy,hv]
  by_cases hys : y∈tsupport χ
  · rw [child_band_indicator_join ha y (hχs hys) hn]
  · rw [image_eq_zero_of_notMem_tsupport hys]
    simp

include hχs in
lemma childLocalComponentCLM_smooth_gradient (f : centralSmoothFunctions) (i : Fin 3) :
    childLocalComponentCLM s hs ha k hχ hc i.succ (centralEmbedL s f)=ᵐ[volume]
      localJoinedGradient (fun y => a*(sourceCollarTime y-(-centralThickness))) χ
        (fun y => f (sourcePairCoordinates (sourceChildCoordinates (actualChildSign k) y)))
        (fun y => (attachedEndPoissonField s (centralSmoothTrace s f k.succ) a (-centralThickness) 0 y).re) i := by
  have he₀ := compactMultiplierCLM_ae ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hc.fderiv_apply ℝ (Pi.single i 1)) (childJoinedComponentCLM s hs ha k 0 (centralEmbedL s f))
  have he₁ := compactMultiplierCLM_ae hχ.continuous hc (childJoinedComponentCLM s hs ha k i.succ (centralEmbedL s f))
  apply (Lp.coeFn_add _ _).trans
  filter_upwards [he₀,he₁,childJoinedComponentCLM_smooth_value s hs ha k f,
    childJoinedComponentCLM_smooth_gradient s hs ha k f i,
    sourceColevel_ae_ne (show -centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])] with y h₀ h₁ hv hg hn
  change (compactMultiplierCLM ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hc.fderiv_apply ℝ (Pi.single i 1)) (childJoinedComponentCLM s hs ha k 0 (centralEmbedL s f))) y+
      (compactMultiplierCLM hχ.continuous hc (childJoinedComponentCLM s hs ha k i.succ (centralEmbedL s f))) y=_
  rw [h₀,h₁,hv,hg]
  simp only [localJoinedGradient]
  by_cases hys : y∈tsupport χ
  · rw [child_band_indicator_join ha y (hχs hys) hn,
      child_band_indicator_join ha y (hχs hys) hn]
  · rw [image_eq_zero_of_notMem_tsupport hys,fderiv_of_notMem_tsupport ℝ hys]
    simp

include hχs in
lemma childLocalJetCLM_smooth_ae (f : centralSmoothFunctions) :
    childLocalJetCLM s hs ha k hχ hc (centralEmbedL s f)=ᵐ[ballMeasure] (fun x =>
      WithLp.toLp 2 (Fin.cases
        (localJoinedValue (fun y => a*(sourceCollarTime y-(-centralThickness))) χ
          (fun y => f (sourcePairCoordinates (sourceChildCoordinates (actualChildSign k) y)))
          (fun y => (attachedEndPoissonField s (centralSmoothTrace s f k.succ) a (-centralThickness) 0 y).re) (WithLp.ofLp x))
        (fun i => localJoinedGradient (fun y => a*(sourceCollarTime y-(-centralThickness))) χ
          (fun y => f (sourcePairCoordinates (sourceChildCoordinates (actualChildSign k) y)))
          (fun y => (attachedEndPoissonField s (centralSmoothTrace s f k.succ) a (-centralThickness) 0 y).re) i (WithLp.ofLp x)))) := by
  have h₀ := ae_restrict_of_ae (s:=ball) ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp
    (childLocalComponentCLM_smooth_value s hs ha k hχ hc hχs f))
  have h₁ (i : Fin 3) := ae_restrict_of_ae (s:=ball) ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp
    (childLocalComponentCLM_smooth_gradient s hs ha k hχ hc hχs f i))
  apply (physicalFourJetCLM_ae (fun i => childLocalComponentCLM s hs ha k hχ hc i (centralEmbedL s f))).trans
  filter_upwards [h₀,ae_all_iff.mpr h₁] with x hv hg
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hv
  · exact hg j

end ScalarConductivity

end

end OAI
