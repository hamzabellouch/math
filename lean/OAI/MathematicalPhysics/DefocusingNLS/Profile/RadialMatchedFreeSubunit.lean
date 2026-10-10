import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedProfileLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeSubunit

namespace OAI

/-! The limiting profile is uniformly subunit away from its flat core. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

theorem radialShootingFreeExterior_norm (z : ProfileMatchingBall) (r : ℝ) :
    ‖radialShootingFreeExterior z r‖=
      ‖(radialFreeSlowJet (radialShootingQ z) (radialShootingM z) (Real.log r)).1‖ := by
  rw [radialShootingFreeExterior,norm_mul]
  have he : ‖Complex.exp ((-2*radialShootingQ z)*(Real.log r : ℂ))‖=1 := by
    simp [Complex.norm_exp,radialShootingQ,Complex.mul_re,Complex.mul_im]
  rw [he,one_mul]

theorem radialMatchedFreeProfile_subunit (z : ProfileMatchingBall) (r : ℝ)
    (hr : radialShootingR (profileMatchingParameter z) < r) :
    ‖radialMatchedFreeProfile z r‖ < 1 := by
  by_cases hi : r ≤ innerBoundaryRadius
  · rw [radialMatchedFreeProfile,ite_eq_left hi,ite_eq_right (not_le.mpr hr)]
    obtain ⟨hb,hl,hu,hlu,hwidth,_⟩ := radialShooting_geometry (profileMatchingParameter z)
    obtain ⟨hJ,hFI,hGI,hbound,_⟩ := radialFreeInnerJet_spec (profileMatchingParameter z)
    exact radial_free_modulus_lt_one _ _ _ hb hl hu hlu hwidth _ _ hJ.fst hJ.snd
      hFI hGI (fun t _ => hbound t) r ⟨hr,hi⟩
  · rw [radialMatchedFreeProfile,ite_eq_right hi,radialShootingFreeExterior_norm]
    obtain ⟨δ,ρ,hδ,_,_,hρ,hupper,_⟩ := radialShooting_free_annulus z
    have hb := hupper (Real.log r)
      (Real.log_le_log (by linarith [innerBoundaryRadius_bounds.1]) (lt_of_not_ge hi).le)
    linarith

theorem radialMatchedFreeProfile_uniform_subunit (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0) (R d : ℝ) (hd : 0 < d) :
    ∃ ρ : ℝ, ρ < 1 ∧ ∀ r ∈ Icc (radialShootingR (profileMatchingParameter z₀)+d) R,
      ‖radialMatchedFreeProfile z₀ r‖ ≤ ρ := by
  let l := radialShootingR (profileMatchingParameter z₀)
  have hl : 0 ≤ l+d := by
    have h := (radialShooting_geometry (profileMatchingParameter z₀)).2.1
    dsimp [l]
    linarith
  have hc := (radialMatchedFreeProfile_continuousOn s hs z z₀ hz hX hm R).mono
    (show Icc (l+d) R ⊆ Icc 0 R from fun r hr => ⟨hl.trans hr.1,hr.2⟩)
  obtain ⟨δ,hδ,hbound⟩ := isCompact_Icc.exists_forall_le'
    (continuousOn_const.sub hc.norm)
    (fun r hr => sub_pos.mpr (radialMatchedFreeProfile_subunit z₀ r (by
      change l < r
      linarith [hr.1])))
  refine ⟨1-δ,by linarith,fun r hr => ?_⟩
  have hb := hbound r hr
  change δ ≤ 1-‖radialMatchedFreeProfile z₀ r‖ at hb
  linarith

end DefocusingNLS

end OAI
