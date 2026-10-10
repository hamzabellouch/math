import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCanonicalParameterL2
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCanonicalParameterSmooth
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTailEnergyLinear

namespace OAI

/-! A fixed combination of the actual parameter columns is an admissible tail correction. -/

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def canonicalParameterValueCombination (ν : ℂ)
    (Y Z : ℂ → ℝ → E₄) (lam : ℂ) (c : ℂ × ℂ) (r : ℝ) : ℂ × ℂ :=
  c.1 • canonicalPhysicalParameterValues ν Y lam r+
    c.2 • canonicalPhysicalParameterValues ν Z lam r

noncomputable def canonicalParameterStateCombination (ν : ℂ)
    (Y Z : ℂ → ℝ → E₄) (lam : ℂ) (c : ℂ × ℂ) (r : ℝ) : E₄ :=
  c.1 • deriv (fun la => spectralPhysicalPair (ν-2*la) (star ν-2*la) (Y la) r) lam+
    c.2 • deriv (fun la => spectralPhysicalPair (ν-2*la) (star ν-2*la) (Z la) r) lam

theorem canonicalParameterStateCombination_value (ν : ℂ)
    (Y Z : ℂ → ℝ → E₄) (lam : ℂ) (c : ℂ × ℂ) (r : ℝ) :
    spectralPhysicalValueMap (canonicalParameterStateCombination ν Y Z lam c r)=
      canonicalParameterValueCombination ν Y Z lam c r := by
  simp only [canonicalParameterStateCombination,map_add,map_smul]
  rfl

theorem radialCanonicalParameter_combination_tail (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (eta : ℂ) (Y Z : ℂ → ℝ → E₄)
    (hY : IsCanonicalHolomorphicColumn (radialShootingNu (n+radialInnerShootingThreshold) z)
      eta (radialShootingM z) (n+radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) (1,0) Y)
    (hZ : IsCanonicalHolomorphicColumn (radialShootingNu (n+radialInnerShootingThreshold) z)
      eta (radialShootingM z) (n+radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) (0,1) Z)
    (lam : ℂ) (hlam : 0≤lam.re) (N : ℕ) (hN : 7≤N) (c : ℂ × ℂ) (R : ℝ) :
    let W := canonicalParameterValueCombination
      (radialShootingNu (n+radialInnerShootingThreshold) z) Y Z lam c
    ∃ T : ℝ, R<T ∧ innerBoundaryRadius<T ∧ ContDiffOn ℝ ∞ W (Ioi T) ∧
      (∃ M : ℝ, 0≤M ∧ ∀ r, T≤r → ‖W r‖≤M) ∧
      IntegrableOn (fun r => r^11*‖iteratedDeriv N W r‖^2) (Ioi T) := by
  intro W
  let ν := radialShootingNu (n+radialInnerShootingThreshold) z
  have hn : 1≤n+radialInnerShootingThreshold := by
    have h := radialShootingInner_power_pos n (profileMatchingParameter z)
    omega
  have hhalf : -(1/32 : ℝ)≤lam.re := by linarith
  obtain ⟨Sy,_,hYs⟩ := canonicalPhysicalParameterValues_smooth_tail ν eta _ _ hn _ hX
    (radialShootingM_ne_zero z) (1,0) Y hY lam
  obtain ⟨Sz,_,hZs⟩ := canonicalPhysicalParameterValues_smooth_tail ν eta _ _ hn _ hX
    (radialShootingM_ne_zero z) (0,1) Z hZ lam
  obtain ⟨Ey,_,hYi⟩ := radialCanonicalParameter_top_integrable n z hX eta (1,0) Y hY lam hhalf N hN
  obtain ⟨Ez,_,hZi⟩ := radialCanonicalParameter_top_integrable n z hX eta (0,1) Z hZ lam hhalf N hN
  obtain ⟨Cy,hCy,hYb⟩ := radialCanonicalParameter_eventually_bounded n z hX eta (1,0) Y hY lam hlam
  obtain ⟨Cz,hCz,hZb⟩ := radialCanonicalParameter_eventually_bounded n z hX eta (0,1) Z hZ lam hlam
  have hall : ∀ᶠ r in atTop, R<r ∧ innerBoundaryRadius<r ∧ Sy≤r ∧ Sz≤r ∧ Ey≤r ∧ Ez≤r ∧
      ‖canonicalPhysicalParameterValues ν Y lam r‖≤Cy ∧
      ‖canonicalPhysicalParameterValues ν Z lam r‖≤Cz := by
    filter_upwards [eventually_gt_atTop R,eventually_gt_atTop innerBoundaryRadius,
      eventually_ge_atTop Sy,eventually_ge_atTop Sz,eventually_ge_atTop Ey,eventually_ge_atTop Ez,
      hYb,hZb] with r hr hi hsy hsz hey hez hy hz
    exact ⟨hr,hi,hsy,hsz,hey,hez,hy,hz⟩
  obtain ⟨T,hT⟩ := eventually_atTop.mp hall
  obtain ⟨hRT,hiT,hsy,hsz,hey,hez,_,_⟩ := hT T le_rfl
  have hYsT := hYs.mono (Ioi_subset_Ioi hsy)
  have hZsT := hZs.mono (Ioi_subset_Ioi hsz)
  have hi₀ : 0 < innerBoundaryRadius := by linarith [innerBoundaryRadius_bounds.1]
  have hT₀ : 0≤T := hi₀.le.trans hiT.le
  refine ⟨T,hRT,hiT,(hYsT.const_smul c.1).add (hZsT.const_smul c.2),?_,?_⟩
  · refine ⟨‖c.1‖*Cy+‖c.2‖*Cz,by positivity,?_⟩
    intro r hr
    obtain ⟨_,_,_,_,_,_,hy,hz⟩ := hT r hr
    change ‖c.1 • canonicalPhysicalParameterValues ν Y lam r+
      c.2 • canonicalPhysicalParameterValues ν Z lam r‖ ≤ _
    apply (norm_add_le _ _).trans
    simp only [norm_smul]
    exact add_le_add (mul_le_mul_of_nonneg_left hy (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hz (norm_nonneg _))
  · exact spectralWeighted_top_combination_integrable _ _ T hT₀ N c.1 c.2 hYsT hZsT
      (hYi.mono_set (Ioi_subset_Ioi hey)) (hZi.mono_set (Ioi_subset_Ioi hez))

end DefocusingNLS

end OAI
