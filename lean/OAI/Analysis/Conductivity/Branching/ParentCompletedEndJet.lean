import Mathlib
import OAI.Analysis.Conductivity.Sobolev.ParentCompletionJoin

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : ℝ} (ha : a<0)

lemma parentCentralComponentCLM_zero_end (u : CentralAmbient s) (i : Fin 4) :
    ∀ᵐ y∂volume,sourceCollarTime y<centralThickness →
      parentCentralComponentCLM s i u y=0 := by
  have he := lpZeroExtensionCLM_ae parentBand_measurable
    (lpRestrictionCLM (sourceClosedCollarBand centralThickness (2*centralThickness))
      (centralPhysicalWholeCLM (centralAmbientComponent s i u)))
  filter_upwards [he] with y hy ht
  rw [show parentCentralComponentCLM s i u y=_ from hy]
  exact indicator_of_notMem (fun hh => not_le_of_gt ht hh.1) _

lemma parentJoinedComponentCLM_end_value (u : CentralAmbient s) :
    ∀ᵐ y∂volume,y∈sourceClosedCollarBand 0 centralThickness →
      parentJoinedComponentCLM s hs ha 0 u y=
        (attachedEndPoissonField s (centralAmbientT s 0 u) a centralThickness 0 y).re := by
  have hadd := Lp.coeFn_add (parentCentralComponentCLM s 0 u)
    (parentEndValueCLM s hs ha (centralAmbientT s 0 u))
  filter_upwards [hadd,parentCentralComponentCLM_zero_end s u 0,
    parentEndValueCLM_ae s hs ha (centralAmbientT s 0 u),
    sourceColevel_ae_ne (show centralThickness∈Icc (-(1:ℝ)/100) (1/100) by
      norm_num [centralThickness])] with y hy hc he hn hb
  change (parentCentralComponentCLM s 0 u+parentEndValueCLM s hs ha (centralAmbientT s 0 u)) y=_
  rw [hy]
  simp only [Pi.add_apply,hc (lt_of_le_of_ne hb.2 hn),he,indicator_of_mem hb,zero_add]

lemma parentJoinedComponentCLM_end_gradient (u : CentralAmbient s) (i : Fin 3) :
    ∀ᵐ y∂volume,y∈sourceClosedCollarBand 0 centralThickness →
      parentJoinedComponentCLM s hs ha i.succ u y=
        fderiv ℝ (fun y => (attachedEndPoissonField s (centralAmbientT s 0 u)
          a centralThickness 0 y).re) y (Pi.single i 1) := by
  have hadd := Lp.coeFn_add (parentCentralComponentCLM s i.succ u)
    (parentEndGradientCLM s hs ha i (centralAmbientT s 0 u))
  filter_upwards [hadd,parentCentralComponentCLM_zero_end s u i.succ,
    parentEndGradientCLM_ae s hs ha (centralAmbientT s 0 u) i,
    sourceColevel_ae_ne (show centralThickness∈Icc (-(1:ℝ)/100) (1/100) by
      norm_num [centralThickness])] with y hy hc he hn hb
  change (parentCentralComponentCLM s i.succ u+parentEndGradientCLM s hs ha i (centralAmbientT s 0 u)) y=_
  rw [hy]
  simp only [Pi.add_apply,hc (lt_of_le_of_ne hb.2 hn),he,indicator_of_mem hb,zero_add]

variable {χ : (Fin 3 → ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
  (hc : HasCompactSupport χ)

lemma parentLocalComponentCLM_end_value (u : CentralAmbient s) :
    ∀ᵐ y∂volume,y∈sourceClosedCollarBand 0 centralThickness →
      parentLocalComponentCLM s hs ha hχ hc 0 u y=
        χ y*(attachedEndPoissonField s (centralAmbientT s 0 u) a centralThickness 0 y).re := by
  filter_upwards [compactMultiplierCLM_ae hχ.continuous hc
    (parentJoinedComponentCLM s hs ha 0 u),
    parentJoinedComponentCLM_end_value s hs ha u] with y he hv hb
  exact he.trans (congrArg (fun z => χ y*z) (hv hb))

lemma parentLocalComponentCLM_end_gradient (u : CentralAmbient s) (i : Fin 3) :
    ∀ᵐ y∂volume,y∈sourceClosedCollarBand 0 centralThickness →
      parentLocalComponentCLM s hs ha hχ hc i.succ u y=
        fderiv ℝ χ y (Pi.single i 1)*
          (attachedEndPoissonField s (centralAmbientT s 0 u) a centralThickness 0 y).re+
        χ y*fderiv ℝ (fun y => (attachedEndPoissonField s (centralAmbientT s 0 u)
          a centralThickness 0 y).re) y (Pi.single i 1) := by
  have h₀ := compactMultiplierCLM_ae
    ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hc.fderiv_apply ℝ (Pi.single i 1)) (parentJoinedComponentCLM s hs ha 0 u)
  have h₁ := compactMultiplierCLM_ae hχ.continuous hc
    (parentJoinedComponentCLM s hs ha i.succ u)
  have hadd := Lp.coeFn_add
    (compactMultiplierCLM ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hc.fderiv_apply ℝ (Pi.single i 1)) (parentJoinedComponentCLM s hs ha 0 u))
    (compactMultiplierCLM hχ.continuous hc (parentJoinedComponentCLM s hs ha i.succ u))
  filter_upwards [hadd,h₀,h₁,parentJoinedComponentCLM_end_value s hs ha u,
    parentJoinedComponentCLM_end_gradient s hs ha u i] with y he h₀ h₁ hv hg hb
  apply he.trans
  simp only [Pi.add_apply,h₀,h₁,hv hb,hg hb]

theorem parentCompletionJoin_end_ae (hχb : ∀ x,|χ x|≤1)
    (hχs : tsupport χ⊆sourceClosedCollarBand 0 (2*centralThickness))
    (p : centralEnergySpace s) :
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈sourceClosedCollarBand 0 centralThickness →
      weakValue (parentCompletionJoin s hs ha hχ hc hχb hχs p) x=
        χ (WithLp.ofLp x)*(attachedEndPoissonField s (centralT s 0 p)
          a centralThickness 0 (WithLp.ofLp x)).re ∧
      ∀ i,weakGradient (parentCompletionJoin s hs ha hχ hc hχb hχs p) x i=
        fderiv ℝ χ (WithLp.ofLp x) (Pi.single i 1)*
          (attachedEndPoissonField s (centralT s 0 p) a centralThickness 0 (WithLp.ofLp x)).re+
        χ (WithLp.ofLp x)*fderiv ℝ (fun y =>
          (attachedEndPoissonField s (centralT s 0 p) a centralThickness 0 y).re)
          (WithLp.ofLp x) (Pi.single i 1) := by
  have h₀ := ae_restrict_of_ae (s:=ball)
    ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
      (parentLocalComponentCLM_end_value s hs ha hχ hc p.val))
  have h₁ (i : Fin 3) := ae_restrict_of_ae (s:=ball)
    ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
      (parentLocalComponentCLM_end_gradient s hs ha hχ hc p.val i))
  have hjet := physicalFourJetCLM_ae
    (fun i => parentLocalComponentCLM s hs ha hχ hc i p.val)
  filter_upwards [hjet,h₀,ae_all_iff.mpr h₁] with x hj hv hg hb
  constructor
  · change WithLp.ofLp ((parentLocalJetCLM s hs ha hχ hc p.val) x) 0=_
    exact (congrArg (fun z : JetFiber => WithLp.ofLp z 0) hj).trans (hv hb)
  · intro i
    change WithLp.ofLp ((parentLocalJetCLM s hs ha hχ hc p.val) x) i.succ=_
    exact (congrArg (fun z : JetFiber => WithLp.ofLp z i.succ) hj).trans (hg i hb)

end ScalarConductivity

end

end OAI
