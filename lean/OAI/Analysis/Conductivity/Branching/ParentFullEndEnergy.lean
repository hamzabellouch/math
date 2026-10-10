import Mathlib
import OAI.Analysis.Conductivity.Variational.FullEndClosedEnergy

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

theorem parentFullEnd_weak_energy_exists (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    {a : ℝ} (ha : a<0) (κ : ℝ) (p : centralEnergySpace s) :
    ∃ w : H1,w∈H10 ∧
      (∀ᵐ x∂ballMeasure,WithLp.ofLp x∈sourceClosedCollarBand 0 centralThickness →
        weakValue w x=fullAttachedEndValue s (centralT s 0 p) a centralThickness κ (WithLp.ofLp x) ∧
        ∀ k,weakGradient w x k=fullAttachedEndGradient s (centralT s 0 p) a centralThickness κ (WithLp.ofLp x) k) ∧
      (∀ (ψ : H1) (i j : Fin 4),
        Integrable (fun y => originalPiGradient w y ⬝ᵥ
          (attachedCollarTensor s a y*ᵥoriginalPiGradient ψ y))
          (volume.restrict (sourceCollarPiece i j '' sourceExtendedBox 0 centralThickness)) ∧
        (∫ y in sourceCollarPiece i j '' sourceExtendedBox 0 centralThickness,
          originalPiGradient w y ⬝ᵥ (attachedCollarTensor s a y*ᵥoriginalPiGradient ψ y))=
          ∫ x in sourceExtendedBox 0 centralThickness,
            |a| *angularArea*faceRayDensity 1 i (x 1)*faceRayDensity sourceRadialWidth j (x 2)*
              (fullEndFlatCovector s (centralT s 0 p) κ (a*(x 0-centralThickness))
                  (torusAngles (sourceFaceAngles i j x)) ⬝ᵥ
                (flatCylinderMatrix s*ᵥ((attachedCartesianMatrix a i j x)⁻¹*ᵥ
                  originalPiGradient ψ (sourceCollarPiece i j x))))) := by
  obtain ⟨w,hw,he⟩ := parentFullEnd_H10 s hs ha κ p
  have hlow : -(1:ℝ)/100≤0 := by norm_num
  have hupp : centralThickness≤(1:ℝ)/100 := by norm_num [centralThickness]
  have hband : sourceClosedCollarBand 0 centralThickness⊆
      sourceClosedCollarBand (-(1:ℝ)/100) (1/100) :=
    fun _ hy => ⟨hlow.trans hy.1,hy.2.trans hupp⟩
  have hjet := originalPiGradient_eq_on hband w
    (fullAttachedEndGradient s (centralT s 0 p) a centralThickness κ)
    (by filter_upwards [he] with x hx hm; exact (hx hm).2)
  refine ⟨w,hw,he,fun ψ i j => ⟨?_,?_⟩⟩
  · exact attachedCollarTensor_weak_integrable s ha.ne
      (sourceCollarClosedPiece_measurable 0 centralThickness i j)
      ((sourceCollarClosedPiece_subset hlow hupp i j).trans hband) w ψ
  · calc
      _ = ∫ y in sourceCollarPiece i j '' sourceExtendedBox 0 centralThickness,
          fullAttachedEndGradient s (centralT s 0 p) a centralThickness κ y ⬝ᵥ
            (attachedCollarTensor s a y*ᵥoriginalPiGradient ψ y) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae hjet,
          ae_restrict_mem (sourceCollarClosedPiece_measurable 0 centralThickness i j)] with y hy hm
        rw [hy (sourceCollarClosedPiece_subset hlow hupp i j hm)]
      _ = _ := fullAttachedEnd_vector_integral_open s hs (centralT s 0 p) κ
        (originalPiGradient ψ) ha.ne i j hlow hupp
        (fun t ht => mul_pos_of_neg_of_neg ha (sub_neg.mpr ht.2))

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : ℝ} (ha : 0<a) (k : Fin 2)

lemma childCentralRawComponentCLM_zero_end (k : Fin 2) (u : CentralAmbient s) (i : Fin 4) :
    ∀ᵐ y∂volume,-centralThickness<sourceCollarTime y →
      childCentralRawComponentCLM s k i u y=0 := by
  have he := lpZeroExtensionCLM_ae childCentralBand_measurable
    (lpRestrictionCLM (sourceClosedCollarBand (-2*centralThickness) (-centralThickness))
      (sourceChildPullbackCLM (actualChildSign k)
        (centralPhysicalWholeCLM (centralAmbientComponent s i u))))
  filter_upwards [he] with y hy ht
  rw [show childCentralRawComponentCLM s k i u y=_ from hy]
  exact indicator_of_notMem (fun hh => not_le_of_gt ht hh.2) _

lemma childCentralComponentCLM_zero_end (k : Fin 2) (u : CentralAmbient s) (i : Fin 4) :
    ∀ᵐ y∂volume,-centralThickness<sourceCollarTime y →
      childCentralComponentCLM s k i u y=0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact childCentralRawComponentCLM_zero_end s k u 0
  · filter_upwards [childCentralRawComponentCLM_zero_end s k u (childAxis j).succ,
      Lp.coeFn_smul sourceScale (childCentralRawComponentCLM s k (childAxis j).succ u)] with y hy he ht
    change (sourceScale • childCentralRawComponentCLM s k (childAxis j).succ u) y=0
    rw [he]
    simp only [Pi.smul_apply,smul_eq_mul,hy ht,mul_zero]

lemma childJoinedComponentCLM_end_value (u : CentralAmbient s) :
    ∀ᵐ y∂volume,y∈sourceClosedCollarBand (-centralThickness) 0 →
      childJoinedComponentCLM s hs ha k 0 u y=
        (attachedEndPoissonField s (centralAmbientT s k.succ u) a (-centralThickness) 0 y).re := by
  have hadd := Lp.coeFn_add (childCentralComponentCLM s k 0 u)
    (childEndValueCLM s hs ha (centralAmbientT s k.succ u))
  filter_upwards [hadd,childCentralComponentCLM_zero_end s k u 0,
    childEndValueCLM_ae s hs ha (centralAmbientT s k.succ u),
    sourceColevel_ae_ne (show -centralThickness∈Icc (-(1:ℝ)/100) (1/100) by
      norm_num [centralThickness])] with y hy hc he hn hb
  change (childCentralComponentCLM s k 0 u+childEndValueCLM s hs ha (centralAmbientT s k.succ u)) y=_
  rw [hy]
  simp only [Pi.add_apply,hc (lt_of_le_of_ne hb.1 (Ne.symm hn)),he,indicator_of_mem hb,zero_add]

lemma childJoinedComponentCLM_end_gradient (u : CentralAmbient s) (i : Fin 3) :
    ∀ᵐ y∂volume,y∈sourceClosedCollarBand (-centralThickness) 0 →
      childJoinedComponentCLM s hs ha k i.succ u y=
        fderiv ℝ (fun y => (attachedEndPoissonField s (centralAmbientT s k.succ u)
          a (-centralThickness) 0 y).re) y (Pi.single i 1) := by
  have hadd := Lp.coeFn_add (childCentralComponentCLM s k i.succ u)
    (childEndGradientCLM s hs ha i (centralAmbientT s k.succ u))
  filter_upwards [hadd,childCentralComponentCLM_zero_end s k u i.succ,
    childEndGradientCLM_ae s hs ha (centralAmbientT s k.succ u) i,
    sourceColevel_ae_ne (show -centralThickness∈Icc (-(1:ℝ)/100) (1/100) by
      norm_num [centralThickness])] with y hy hc he hn hb
  change (childCentralComponentCLM s k i.succ u+childEndGradientCLM s hs ha i (centralAmbientT s k.succ u)) y=_
  rw [hy]
  simp only [Pi.add_apply,hc (lt_of_le_of_ne hb.1 (Ne.symm hn)),he,indicator_of_mem hb,zero_add]

variable {χ : (Fin 3 → ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
  (hc : HasCompactSupport χ)

lemma childLocalComponentCLM_end_value (u : CentralAmbient s) :
    ∀ᵐ y∂volume,y∈sourceClosedCollarBand (-centralThickness) 0 →
      childLocalComponentCLM s hs ha k hχ hc 0 u y=
        χ y*(attachedEndPoissonField s (centralAmbientT s k.succ u) a (-centralThickness) 0 y).re := by
  filter_upwards [compactMultiplierCLM_ae hχ.continuous hc
    (childJoinedComponentCLM s hs ha k 0 u),
    childJoinedComponentCLM_end_value s hs ha k u] with y he hv hb
  exact he.trans (congrArg (fun z => χ y*z) (hv hb))

lemma childLocalComponentCLM_end_gradient (u : CentralAmbient s) (i : Fin 3) :
    ∀ᵐ y∂volume,y∈sourceClosedCollarBand (-centralThickness) 0 →
      childLocalComponentCLM s hs ha k hχ hc i.succ u y=
        fderiv ℝ χ y (Pi.single i 1)*
          (attachedEndPoissonField s (centralAmbientT s k.succ u) a (-centralThickness) 0 y).re+
        χ y*fderiv ℝ (fun y => (attachedEndPoissonField s (centralAmbientT s k.succ u)
          a (-centralThickness) 0 y).re) y (Pi.single i 1) := by
  have h₀ := compactMultiplierCLM_ae
    ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hc.fderiv_apply ℝ (Pi.single i 1)) (childJoinedComponentCLM s hs ha k 0 u)
  have h₁ := compactMultiplierCLM_ae hχ.continuous hc
    (childJoinedComponentCLM s hs ha k i.succ u)
  have hadd := Lp.coeFn_add
    (compactMultiplierCLM ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hc.fderiv_apply ℝ (Pi.single i 1)) (childJoinedComponentCLM s hs ha k 0 u))
    (compactMultiplierCLM hχ.continuous hc (childJoinedComponentCLM s hs ha k i.succ u))
  filter_upwards [hadd,h₀,h₁,childJoinedComponentCLM_end_value s hs ha k u,
    childJoinedComponentCLM_end_gradient s hs ha k u i] with y he h₀ h₁ hv hg hb
  apply he.trans
  simp only [Pi.add_apply,h₀,h₁,hv hb,hg hb]

theorem childCompletionJoin_end_ae (hχb : ∀ x,|χ x|≤1)
    (hχs : tsupport χ⊆sourceClosedCollarBand (-2*centralThickness) 0)
    (p : centralEnergySpace s) :
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈sourceClosedCollarBand (-centralThickness) 0 →
      weakValue (childCompletionJoin s hs ha k hχ hc hχb hχs p) x=
        χ (WithLp.ofLp x)*(attachedEndPoissonField s (centralT s k.succ p)
          a (-centralThickness) 0 (WithLp.ofLp x)).re ∧
      ∀ i,weakGradient (childCompletionJoin s hs ha k hχ hc hχb hχs p) x i=
        fderiv ℝ χ (WithLp.ofLp x) (Pi.single i 1)*
          (attachedEndPoissonField s (centralT s k.succ p) a (-centralThickness) 0 (WithLp.ofLp x)).re+
        χ (WithLp.ofLp x)*fderiv ℝ (fun y =>
          (attachedEndPoissonField s (centralT s k.succ p) a (-centralThickness) 0 y).re)
          (WithLp.ofLp x) (Pi.single i 1) := by
  have h₀ := ae_restrict_of_ae (s:=ball)
    ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
      (childLocalComponentCLM_end_value s hs ha k hχ hc p.val))
  have h₁ (i : Fin 3) := ae_restrict_of_ae (s:=ball)
    ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
      (childLocalComponentCLM_end_gradient s hs ha k hχ hc p.val i))
  have hjet := physicalFourJetCLM_ae
    (fun i => childLocalComponentCLM s hs ha k hχ hc i p.val)
  filter_upwards [hjet,h₀,ae_all_iff.mpr h₁] with x hj hv hg hb
  constructor
  · change WithLp.ofLp ((childLocalJetCLM s hs ha k hχ hc p.val) x) 0=_
    exact (congrArg (fun z : JetFiber => WithLp.ofLp z 0) hj).trans (hv hb)
  · intro i
    change WithLp.ofLp ((childLocalJetCLM s hs ha k hχ hc p.val) x) i.succ=_
    exact (congrArg (fun z : JetFiber => WithLp.ofLp z i.succ) hj).trans (hg i hb)

end ScalarConductivity

end

end OAI
