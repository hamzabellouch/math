import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCanonicalParameterCombination
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTailEnergyPair
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousOutgoingRadialRows

namespace OAI

/-! Subtracting the parameter correction preserves the generalized mode's tail energy. -/

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem radialCanonicalParameter_remainder_energy (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (eta : ℂ) (Y Z : ℂ → ℝ → E₄)
    (hY : IsCanonicalHolomorphicColumn (radialShootingNu (n+radialInnerShootingThreshold) z)
      eta (radialShootingM z) (n+radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) (1,0) Y)
    (hZ : IsCanonicalHolomorphicColumn (radialShootingNu (n+radialInnerShootingThreshold) z)
      eta (radialShootingM z) (n+radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) (0,1) Z)
    (lam : ℂ) (hlam : 0≤lam.re) (N : ℕ) (hN : 7≤N) (c : ℂ × ℂ) (R : ℝ)
    (v w : ℝ → ℂ) (hv : ContDiffOn ℝ ∞ v (Ioi 0)) (hw : ContDiffOn ℝ ∞ w (Ioi 0))
    (hvt : IntegrableOn (fun r => r^11*‖iteratedDeriv N v r‖^2) (Ioi 0))
    (hwt : IntegrableOn (fun r => r^11*‖iteratedDeriv N w r‖^2) (Ioi 0))
    (hb : ∃ M : ℝ, 0≤M ∧ ∀ r, ‖(v r,w r)‖≤M) :
    let H := fun r => (v r,w r)-canonicalParameterValueCombination
      (radialShootingNu (n+radialInnerShootingThreshold) z) Y Z lam c r
    ∃ T : ℝ, R<T ∧ innerBoundaryRadius<T ∧ ContDiffOn ℝ ∞ H (Ioi T) ∧
      (∃ M : ℝ, 0≤M ∧ ∀ r, T≤r → ‖H r‖≤M) ∧
      IntegrableOn (fun r => r^11*‖(iteratedDeriv N H r).1‖^2) (Ioi T) ∧
      IntegrableOn (fun r => r^11*‖(iteratedDeriv N H r).2‖^2) (Ioi T) := by
  intro H
  let U := fun r => (v r,w r)
  have hUs : ContDiffOn ℝ ∞ U (Ioi 0) := hv.prodMk hw
  have hUd := (homogeneousPair_iteratedDeriv_smooth_tail U 0 hUs N).continuousOn
  have hUp : IntegrableOn (fun r => r^11*‖(iteratedDeriv N U r).1‖^2) (Ioi 0) := by
    apply hvt.congr_fun _ measurableSet_Ioi
    intro r hr
    dsimp only [U]
    rw [homogeneousPair_iteratedDeriv v w hv hw N r hr]
  have hUm : IntegrableOn (fun r => r^11*‖(iteratedDeriv N U r).2‖^2) (Ioi 0) := by
    apply hwt.congr_fun _ measurableSet_Ioi
    intro r hr
    dsimp only [U]
    rw [homogeneousPair_iteratedDeriv v w hv hw N r hr]
  have hUi := spectralWeighted_pair_integrable (iteratedDeriv N U) 0 le_rfl hUd hUp hUm
  obtain ⟨T,hRT,hiT,hDs,⟨MD,hMD,hDb⟩,hDi⟩ :=
    radialCanonicalParameter_combination_tail n z hX eta Y Z hY hZ lam hlam N hN c R
  have hi₀ : 0 < innerBoundaryRadius := by linarith [innerBoundaryRadius_bounds.1]
  have hT₀ : 0≤T := hi₀.le.trans hiT.le
  have hUsT := hUs.mono (Ioi_subset_Ioi hT₀)
  have hHs : ContDiffOn ℝ ∞ H (Ioi T) := hUsT.sub hDs
  have hHi := spectralWeighted_top_sub_integrable U _ T hT₀ N hUsT hDs
    (hUi.mono_set (Ioi_subset_Ioi hT₀)) hDi
  have hHd := (homogeneousPair_iteratedDeriv_smooth_tail H T hHs N).continuousOn
  refine ⟨T,hRT,hiT,hHs,?_,?_,?_⟩
  · obtain ⟨M,hM,hUb⟩ := hb
    refine ⟨M+MD,add_nonneg hM hMD,?_⟩
    intro r hr
    exact (norm_sub_le _ _).trans (add_le_add (hUb r) (hDb r hr))
  · exact spectralWeighted_scalar_of_pair (iteratedDeriv N H) _ T hT₀ hHd.fst
      (fun r _ => norm_fst_le _) hHi
  · exact spectralWeighted_scalar_of_pair (iteratedDeriv N H) _ T hT₀ hHd.snd
      (fun r _ => norm_snd_le _) hHi

end DefocusingNLS

end OAI
