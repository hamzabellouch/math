import OAI.Geometry.Immersion.ClosedSurface.LocalPhaseData
import OAI.Geometry.Immersion.ClosedSurface.LengthMargins
import OAI.Geometry.Immersion.ClosedSurface.SmoothCoordinates

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry

lemma norm_pullCovector_le (A : Base →L[ℝ] Base) (ξ : Base) :
    ‖pullCovector A ξ‖ ≤ 2*‖A‖*‖ξ‖ := by
  have hd : ‖dx‖ = 1 := by simp [dx,Prod.norm_def]
  have he : ‖dy‖ = 1 := by simp [dy,Prod.norm_def]
  have bound (v : Base) (hv : ‖v‖ = 1) : |ξ.1*(A v).1+ξ.2*(A v).2| ≤ 2*‖A‖*‖ξ‖ := by
    have hA : ‖A v‖ ≤ ‖A‖ := by simpa only [hv,mul_one] using A.le_opNorm v
    have h1 : |ξ.1*(A v).1| ≤ ‖ξ‖*‖A‖ := by
      rw [abs_mul]
      exact mul_le_mul (by simpa using norm_fst_le ξ)
        ((show |(A v).1| ≤ ‖A v‖ by simpa using norm_fst_le (A v)).trans hA) (abs_nonneg _) (norm_nonneg _)
    have h2 : |ξ.2*(A v).2| ≤ ‖ξ‖*‖A‖ := by
      rw [abs_mul]
      exact mul_le_mul (by simpa using norm_snd_le ξ)
        ((show |(A v).2| ≤ ‖A v‖ by simpa using norm_snd_le (A v)).trans hA) (abs_nonneg _) (norm_nonneg _)
    linarith [abs_add_le (ξ.1*(A v).1) (ξ.2*(A v).2)]
  change max ‖ξ.1*(A dx).1+ξ.2*(A dx).2‖ ‖ξ.1*(A dy).1+ξ.2*(A dy).2‖ ≤ _
  simpa only [Real.norm_eq_abs,max_le_iff] using And.intro (bound dx hd) (bound dy he)




theorem quantitative_chart_phase_margin {F : RField 4} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (ξ p : Base)
    {d C ε : ℝ} (hd : 0 < d) (hC : 0 < C) (hε : 0 < ε)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : d ≤ |coordDet (fderiv ℝ φ p)|) (hA : ‖fderiv ℝ φ p‖ ≤ C)
    (hB : realSecondTensor F (φ p) ≠ 0)
    (hmargin : ε*‖realSecondTensor F (φ p)‖ ≤
      ‖secondQuadratic (realSecondTensor F (φ p)) (-ξ.2,ξ.1)‖) :
    ‖pullCovector (fderiv ℝ φ p) ξ‖ ≤ 2*C*‖ξ‖ ∧
    d^2*ε/(4*C ^ 2)*‖realSecondTensor (F ∘ φ) p‖ ≤
      ‖secondQuadratic (realSecondTensor (F ∘ φ) p)
        (-(pullCovector (fderiv ℝ φ p) ξ).2,(pullCovector (fderiv ℝ φ p) ξ).1)‖ ∧
    Good (realSecondTensor (F ∘ φ) p) (pullCovector (fderiv ℝ φ p) ξ) ∧
    realSecondTensor (F ∘ φ) p ≠ 0 := by
  have hdet0 : coordDet (fderiv ℝ φ p) ≠ 0 := abs_pos.mp (hd.trans_le hdet)
  have hsq : d^2 ≤ (coordDet (fderiv ℝ φ p))^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ hd.le hdet 2
  have hbc : ‖realSecondTensor (F ∘ φ) p‖ ≤ 4*‖realSecondTensor F (φ p)‖*C ^ 2 := by
    apply (norm_realSecondTensor_comp_smooth hF hφ p hD hdet0).trans
    gcongr
  have hlength := norm_phase_length_comp_smooth hF hφ ξ p hD hdet0
  have hbound : d^2*ε/(4*C ^ 2)*‖realSecondTensor (F ∘ φ) p‖ ≤
      ‖secondQuadratic (realSecondTensor (F ∘ φ) p)
        (-(pullCovector (fderiv ℝ φ p) ξ).2,(pullCovector (fderiv ℝ φ p) ξ).1)‖ := by
    rw [hlength]
    calc
      _ ≤ d^2*ε/(4*C ^ 2)*(4*‖realSecondTensor F (φ p)‖*C ^ 2) := by gcongr
      _ = d^2*(ε*‖realSecondTensor F (φ p)‖) := by field_simp
      _ ≤ d^2*‖secondQuadratic (realSecondTensor F (φ p)) (-ξ.2,ξ.1)‖ := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_right hsq (norm_nonneg _)
  have hpos : 0 < ‖secondQuadratic (realSecondTensor (F ∘ φ) p)
        (-(pullCovector (fderiv ℝ φ p) ξ).2,(pullCovector (fderiv ℝ φ p) ξ).1)‖ := by
    rw [hlength]
    exact mul_pos (sq_pos_of_ne_zero hdet0) ((mul_pos hε (norm_pos_iff.mpr hB)).trans_le hmargin)
  refine ⟨(norm_pullCovector_le _ _).trans ?_,hbound,good_of_direction_length_pos _ _ hpos,?_⟩
  · gcongr
  · intro hz
    simp only [hz,secondQuadratic,Pi.zero_apply,smul_zero,add_zero,norm_zero] at hpos
    exact lt_irrefl 0 hpos

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry Set Filter

lemma gramDet_comp_smooth {F : RField 4} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (p : Base) :
    NormalFrame.gramDet (coordDeriv dx (F ∘ φ) p) (coordDeriv dy (F ∘ φ) p) =
    ((fderiv ℝ φ p dx).1*(fderiv ℝ φ p dy).2-
      (fderiv ℝ φ p dx).2*(fderiv ℝ φ p dy).1)^2 *
      NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) := by
  rw [coordDeriv_comp_smooth hF hφ,coordDeriv_comp_smooth hF hφ]
  change NormalFrame.gramDet (coordDeriv (fderiv ℝ φ p dx) F (φ p))
    (coordDeriv (fderiv ℝ φ p dy) F (φ p)) = _
  rw [coordDeriv_eq_basis F (fderiv ℝ φ p dx),coordDeriv_eq_basis F (fderiv ℝ φ p dy),
    gramDet_change_basis]

theorem realSecondForm_comp_on {F : RField 4} {φ : Base → Base}
    {U V : Set Base} (hU : IsOpen U) (hV : IsOpen V)
    (hF : ContDiffOn ℝ ∞ F V) (hφ : ContDiffOn ℝ ∞ φ U)
    {p : Base} (hp : p ∈ U) (hφp : φ p ∈ V) (v w : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : (fderiv ℝ φ p dx).1*(fderiv ℝ φ p dy).2-
      (fderiv ℝ φ p dx).2*(fderiv ℝ φ p dy).1 ≠ 0) :
    realSecondForm (F ∘ φ) v w p =
      realSecondForm F (fderiv ℝ φ p v) (fderiv ℝ φ p w) (φ p) := by
  obtain ⟨G,hG,_,_,heG⟩ := smooth_extension_near hV hF.contMDiffOn hφp
  obtain ⟨Φ,hΦ,_,_,heΦ⟩ := smooth_extension_near hU hφ.contMDiffOn hp
  have ep := heΦ.eq_of_nhds
  have eD := heΦ.fderiv_eq (𝕜 := ℝ)
  have hc : ContinuousAt φ p := (hφ p hp).contDiffAt (hU.mem_nhds hp) |>.continuousAt
  have hecomp : G ∘ Φ =ᶠ[𝓝 p] F ∘ φ := by
    filter_upwards [heΦ,heG.comp_tendsto hc] with q hqΦ hqG
    simpa only [Function.comp_apply,hqΦ] using hqG
  have hDG : NormalFrame.gramDet (coordDeriv dx G (Φ p)) (coordDeriv dy G (Φ p)) ≠ 0 := by
    rw [ep,(coordDeriv_eventuallyEq heG dx).eq_of_nhds,
      (coordDeriv_eventuallyEq heG dy).eq_of_nhds]
    exact hD
  have hdetΦ : (fderiv ℝ Φ p dx).1*(fderiv ℝ Φ p dy).2-
      (fderiv ℝ Φ p dx).2*(fderiv ℝ Φ p dy).1 ≠ 0 := by rwa [eD]
  have h := realSecondForm_comp_smooth hG.contDiff hΦ.contDiff v w p hDG hdetΦ
  rw [(realSecondForm_eventuallyEq hecomp v w).eq_of_nhds,eD,ep] at h
  rw [(realSecondForm_eventuallyEq heG _ _).eq_of_nhds] at h
  exact h

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry Set Filter




theorem quantitative_chart_phase_margin_on {F : RField 4} {φ : Base → Base}
    {U V : Set Base} (hU : IsOpen U) (hV : IsOpen V)
    (hF : ContDiffOn ℝ ∞ F V) (hφ : ContDiffOn ℝ ∞ φ U)
    {p : Base} (hp : p ∈ U) (hφp : φ p ∈ V) (ξ : Base)
    {d C ε : ℝ} (hd : 0 < d) (hC : 0 < C) (hε : 0 < ε)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : d ≤ |coordDet (fderiv ℝ φ p)|) (hA : ‖fderiv ℝ φ p‖ ≤ C)
    (hB : realSecondTensor F (φ p) ≠ 0)
    (hmargin : ε*‖realSecondTensor F (φ p)‖ ≤
      ‖secondQuadratic (realSecondTensor F (φ p)) (-ξ.2,ξ.1)‖) :
    ‖pullCovector (fderiv ℝ φ p) ξ‖ ≤ 2*C*‖ξ‖ ∧
    d^2*ε/(4*C ^ 2)*‖realSecondTensor (F ∘ φ) p‖ ≤
      ‖secondQuadratic (realSecondTensor (F ∘ φ) p)
        (-(pullCovector (fderiv ℝ φ p) ξ).2,(pullCovector (fderiv ℝ φ p) ξ).1)‖ ∧
    Good (realSecondTensor (F ∘ φ) p) (pullCovector (fderiv ℝ φ p) ξ) ∧
    realSecondTensor (F ∘ φ) p ≠ 0 := by
  obtain ⟨G,hG,_,_,heG⟩ := smooth_extension_near hV hF.contMDiffOn hφp
  obtain ⟨Φ,hΦ,_,_,heΦ⟩ := smooth_extension_near hU hφ.contMDiffOn hp
  have ep := heΦ.eq_of_nhds
  have eD := heΦ.fderiv_eq (𝕜 := ℝ)
  have hc : ContinuousAt φ p := (hφ p hp).contDiffAt (hU.mem_nhds hp) |>.continuousAt
  have hecomp : G ∘ Φ =ᶠ[𝓝 p] F ∘ φ := by
    filter_upwards [heΦ,heG.comp_tendsto hc] with q hqΦ hqG
    simpa only [Function.comp_apply,hqΦ] using hqG
  have hDG : NormalFrame.gramDet (coordDeriv dx G (Φ p)) (coordDeriv dy G (Φ p)) ≠ 0 := by
    rw [ep,(coordDeriv_eventuallyEq heG dx).eq_of_nhds,
      (coordDeriv_eventuallyEq heG dy).eq_of_nhds]
    exact hD
  have hTG := (realSecondTensor_eventuallyEq heG).eq_of_nhds
  have hTF := (realSecondTensor_eventuallyEq hecomp).eq_of_nhds
  have h := quantitative_chart_phase_margin hG.contDiff hΦ.contDiff ξ p hd hC hε hDG
    (by simpa only [eD] using hdet) (by simpa only [eD] using hA)
    (by simpa only [ep,hTG] using hB) (by simpa only [ep,hTG] using hmargin)
  simpa only [eD,hTF] using h

end ClosedSurfaceR4.RealModes

end

end OAI
