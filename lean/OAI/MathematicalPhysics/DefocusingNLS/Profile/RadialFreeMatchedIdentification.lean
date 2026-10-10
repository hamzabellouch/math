import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreePhysicalLog
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeUniqueness

namespace OAI

/-! At a limiting matching zero, the inner IVP and the outgoing H profile coincide. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate

theorem radialFreeInner_physical (z : ProfileMatchingBall)
    (hz : diskProfile (profileMatchingParameter z)=0) :
    let L := radialShootingR (profileMatchingParameter z)
    EqOn (fun r => (radialFreeInnerJet (profileMatchingParameter z) r).1)
      (fun r => radialShootingFreeExterior z r/radialShootingFreeExterior z L)
      (Icc L innerBoundaryRadius) := by
  intro L
  let Q := radialShootingFreeExterior z
  let F := fun r => Q (max L r)/Q L
  let G := fun r => deriv Q (max L r)/Q L
  have hL : 0 < L := by dsimp only [L]; linarith [(radialShooting_geometry (profileMatchingParameter z)).2.1]
  have hQ (r : ℝ) (hr : 0 < r) := radialShootingFreeExterior_hasDerivAt z r hr
  have hD (r : ℝ) (hr : 0 < r) := radialShootingFreeExterior_hasDerivAt_deriv z r hr
  have hQc : ContinuousOn Q (Ioi 0) := fun r hr => (hQ r hr).continuousAt.continuousWithinAt
  have hDc : ContinuousOn (deriv Q) (Ioi 0) := fun r hr => (hD r hr).continuousAt.continuousWithinAt
  have hF : Continuous F :=
    (hQc.comp_continuous (continuous_const.max continuous_id)
      (fun r => hL.trans_le (le_max_left L r))).div_const _
  have hG : Continuous G :=
    (hDc.comp_continuous (continuous_const.max continuous_id)
      (fun r => hL.trans_le (le_max_left L r))).div_const _
  have hne : Q L ≠ 0 := radialShootingFreeExterior_ne_zero z L le_rfl
  have hF₀ : F L=1 := by simp only [F,max_self,div_self hne]
  have hG₀ : G L=0 := by
    dsimp only [G]
    rw [max_self]
    change deriv (radialShootingFreeExterior z) L/radialShootingFreeExterior z L=0
    rw [radialShootingFreeExterior_neumann z hz,zero_div]
  have hDE (r : ℝ) (hr : r ∈ Ioo L innerBoundaryRadius) :
      HasDerivAt F (G r) r ∧ HasDerivAt G
        (-radialFreeCoefficient r*G r-(radialShootingB (profileMatchingParameter z) : ℂ)*F r) r := by
    have heF : F =ᶠ[nhds r] fun t => Q t/Q L := by
      filter_upwards [Ioi_mem_nhds hr.1] with t ht
      change L < t at ht
      simp only [F,max_eq_right ht.le]
    have heG : G =ᶠ[nhds r] fun t => deriv Q t/Q L := by
      filter_upwards [Ioi_mem_nhds hr.1] with t ht
      change L < t at ht
      simp only [G,max_eq_right ht.le]
    have hQd : deriv Q r=(radialShootingFreeJet z r).2 := (hQ r (hL.trans hr.1)).deriv
    constructor
    · simpa only [G,max_eq_right hr.1.le,hQd] using
        ((hQ r (hL.trans hr.1)).div_const (Q L)).congr_of_eventuallyEq heF
    · apply (((hD r (hL.trans hr.1)).div_const (Q L)).congr_of_eventuallyEq heG).congr_deriv
      dsimp only [F,G]
      rw [max_eq_right hr.1.le]
      ring
  obtain ⟨hFI,hGI⟩ := radial_free_integral_of_derivatives
    (radialShootingB (profileMatchingParameter z)) L innerBoundaryRadius hL F G hF hG hF₀ hG₀ hDE
  have hS := radial_free_components_state (radialShootingB (profileMatchingParameter z))
    L innerBoundaryRadius hL F G hF hG 1 0 hFI (by simpa only [zero_add] using hGI)
  obtain ⟨hJ,hJI,hJD,_⟩ := radialFreeInnerJet_spec (profileMatchingParameter z)
  have hT := radial_free_components_state (radialShootingB (profileMatchingParameter z))
    L innerBoundaryRadius hL _ _ hJ.fst hJ.snd 1 0 hJI (by simpa only [zero_add] using hJD)
  have hp := radialShooting_geometry (profileMatchingParameter z)
  have he := radial_free_integral_unique (radialShootingB (profileMatchingParameter z))
    L innerBoundaryRadius hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1
    (radialFreeInnerJet (profileMatchingParameter z)) (fun r => (F r,G r)) hJ (hF.prodMk hG) hT hS
  intro r hr
  have hv := congrArg Prod.fst (he hr)
  simpa only [F,max_eq_right hr.1] using hv

theorem radialShootingFreeExterior_core_value (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0) :
    radialShootingFreeExterior z (radialShootingR (profileMatchingParameter z))=1 := by
  have hp := radialShooting_geometry (profileMatchingParameter z)
  have he := radialFreeInner_physical z hz ⟨hp.2.2.2.1,le_rfl⟩
  dsimp only at he
  rw [radialShootingFreeExterior_boundary z hz₁] at he
  have hne := radialFreeInner_boundary_ne_zero (profileMatchingParameter z)
  have hq := radialShootingFreeExterior_ne_zero z (radialShootingR (profileMatchingParameter z)) le_rfl
  have hmul := (eq_div_iff hq).mp he
  apply mul_left_cancel₀ hne
  simpa only [mul_one] using hmul

theorem radialMatchedFreeProfile_eq_physical (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (r : ℝ) (hr : radialShootingR (profileMatchingParameter z) ≤ r) :
    radialMatchedFreeProfile z r=radialShootingFreeExterior z r := by
  by_cases hb : r ≤ innerBoundaryRadius
  · rcases hr.eq_or_lt with hr | hr
    · rw [← hr,radialShootingFreeExterior_core_value z hz₁ hz]
      simp only [radialMatchedFreeProfile,ite_eq_left (radialShooting_geometry (profileMatchingParameter z)).2.2.2.1,
        ite_eq_left le_rfl]
    · rw [radialMatchedFreeProfile,ite_eq_left hb,ite_eq_right (not_le.mpr hr)]
      have he := radialFreeInner_physical z hz ⟨hr.le,hb⟩
      simpa only [radialShootingFreeExterior_core_value z hz₁ hz,div_one] using he
  · simp only [radialMatchedFreeProfile,ite_eq_right hb]

end DefocusingNLS

end OAI
