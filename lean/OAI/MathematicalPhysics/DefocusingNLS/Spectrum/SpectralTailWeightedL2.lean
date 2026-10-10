import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTailPowerBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace OAI

/-! A strict physical power bound gives finite weighted top energy on a tail. -/

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace DefocusingNLS
local notation "V" => ℂ × ℂ

theorem spectral_tail_top_integrable (U : ℝ → V) (N : ℕ) (R s : ℝ)
    (hU : ContDiffOn ℝ ∞ U (Ioi R)) (hs : 11+2*s < -1)
    (hb : ∃ C : ℝ, 0≤C ∧ ∀ᶠ r in atTop, ‖iteratedDeriv N U r‖≤C*r^s) :
    ∃ T : ℝ, R<T ∧ 1<T ∧
      IntegrableOn (fun r => r^11*‖iteratedDeriv N U r‖^2) (Ioi T) := by
  obtain ⟨C,hC,hb⟩ := hb
  obtain ⟨B,hB⟩ := eventually_atTop.mp hb
  let T := max R (max B 1)+1
  have hRT : R<T := by dsimp only [T]; linarith [le_max_left R (max B 1)]
  have hBT : B<T := by dsimp only [T]; linarith [(le_max_left B 1).trans (le_max_right R (max B 1))]
  have hT : 1<T := by dsimp only [T]; linarith [(le_max_right B 1).trans (le_max_right R (max B 1))]
  have hT₀ : 0<T := lt_trans zero_lt_one hT
  have hc := (homogeneousPair_iteratedDeriv_smooth_tail U R hU N).continuousOn
  have hcT : ContinuousOn (fun r : ℝ => r^11*‖iteratedDeriv N U r‖^2) (Ioi T) :=
    (continuousOn_id.pow 11).mul
      (((hc.mono (Ioi_subset_Ioi hRT.le)).norm).pow 2)
  refine ⟨T,hRT,hT,?_⟩
  have hi := (integrableOn_Ioi_rpow_of_lt hs hT₀).const_mul (C^2)
  apply hi.mono' (hcT.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr₀ : 0<r := hT₀.trans hr
  have hp : r^(11+2*s)=r^11*(r^s)^2 := by
    rw [Real.rpow_add hr₀,show (2 : ℝ)*s=s*2 by ring,Real.rpow_mul hr₀.le]
    norm_num
  have hsq := pow_le_pow_left₀ (norm_nonneg (iteratedDeriv N U r))
    (hB r (hBT.le.trans hr.le)) 2
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),hp]
  calc
    _ ≤ r^11*(C*r^s)^2 := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by ring

theorem spectralPowerValues_top_integrable (νp νm : ℂ) (hsame : νp.re=νm.re)
    (f g : ℝ → ℂ) (σ : ℝ) (hf : HasLogJetBound σ f) (hg : HasLogJetBound σ g)
    (N : ℕ) (hs : 11+2*(νp.re+σ-(N : ℝ)) < -1) :
    ∃ T : ℝ, 1<T ∧
      IntegrableOn (fun r => r^11*‖iteratedDeriv N (spectralPowerValues νp νm f g) r‖^2)
        (Ioi T) := by
  obtain ⟨Lf,hfs⟩ := hf.smooth
  obtain ⟨Lg,hgs⟩ := hg.smooth
  have hU := spectralPowerValues_smooth νp νm f g (max Lf Lg)
    (hfs.mono (Ioi_subset_Ioi (le_max_left _ _)))
    (hgs.mono (Ioi_subset_Ioi (le_max_right _ _)))
  obtain ⟨T,_,hT,hi⟩ := spectral_tail_top_integrable _ N _ _ hU hs
    (spectralPowerValues_derivative_bound νp νm hsame f g σ hf hg N)
  exact ⟨T,hT,hi⟩

end DefocusingNLS

end OAI
