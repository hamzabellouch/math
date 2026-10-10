import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSobolevEnergy
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCompactEnergyBound
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLocalEnergyGraph
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialEnergyNorm

namespace OAI

/-! Uniform Sobolev bounds for the actual localized sections. Together
with the proved supported compact inclusion, these control the core
localization by its hyperbolic energy graph norm. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment.LocalSobolev

lemma functionEnergy_integrable {f : ℂ × ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    Integrable (fun y => ‖f y‖^2+cubicThetaFunctionEnergy f y) := by
  have hv : Continuous (fun y => ‖f y‖^2) := hf.continuous.norm.pow 2
  have he : Continuous (cubicThetaFunctionEnergy f) := cubicThetaFunctionEnergy_continuous hf
  have hvc : HasCompactSupport (fun y => ‖f y‖^2) :=
    hc.comp_left (g:=fun z : ℂ => ‖z‖^2) (by simp)
  have hec : HasCompactSupport (cubicThetaFunctionEnergy f) := cubicThetaFunctionEnergy_compact hc
  have hi : Integrable (fun y => ‖f y‖^2) (volume : Measure (ℂ × ℝ)) :=
    hv.integrable_of_hasCompactSupport hvc
  have hei : Integrable (cubicThetaFunctionEnergy f) (volume : Measure (ℂ × ℝ)) :=
    he.integrable_of_hasCompactSupport hec
  exact hi.add hei

lemma compact_sobolev_bound {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (hpos : K⊆{y : ℂ × ℝ | 0<y.2}) :
    ∃ C≥0, ∀ (f : ℂ × ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f),
      tsupport f⊆K → ‖(realH1 f hf hc,imagH1 f hf hc)‖^2≤
        C*(∫ y, ‖cubicThetaLocalEnergyJet f y‖^2) := by
  obtain ⟨C,hC,hbound⟩ := cubicThetaCompact_euclideanEnergy_bound hK hpos
  refine ⟨C,hC,fun f hf hc hs => ?_⟩
  have hjet := (cubicThetaLocalEnergyJet_memLp hf hc (hs.trans hpos)).integrable_norm_pow
    (by norm_num)
  have hi := integral_mono (functionEnergy_integrable hf hc) (hjet.const_mul C) (hbound f hs)
  rw [integral_const_mul] at hi
  exact (sobolev_pair_norm_sq_le f hf hc).trans hi

def localizedPair {φ : ℂ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hp : tsupport φ⊆{y : ℂ × ℝ | 0<y.2})
    (F : cubicThetaSmoothTests) :=
  (realH1 (cubicThetaTestLocalization φ F)
      ((cubicThetaTestLocalization_smooth hφ hp F).of_le (by simp))
      (cubicThetaTestLocalization_compact hc F),
    imagH1 (cubicThetaTestLocalization φ F)
      ((cubicThetaTestLocalization_smooth hφ hp F).of_le (by simp))
      (cubicThetaTestLocalization_compact hc F))

lemma localizedPair_bound {φ : ℂ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hp : tsupport φ⊆{y : ℂ × ℝ | 0<y.2}) :
    ∃ C≥0, ∀ F : cubicThetaSmoothTests,
      ‖localizedPair hφ hc hp F‖^2≤C*‖cubicThetaLocalEnergyGraph hφ hc hp F‖^2 := by
  obtain ⟨C,hC,hbound⟩ := compact_sobolev_bound hc hp
  refine ⟨C,hC,fun F => ?_⟩
  have h := hbound (cubicThetaTestLocalization φ F)
    ((cubicThetaTestLocalization_smooth hφ hp F).of_le (by simp))
    (cubicThetaTestLocalization_compact hc F) tsupport_mul_subset_left
  have hn : ‖cubicThetaLocalEnergyGraph hφ hc hp F‖^2=
      ∫ y, ‖cubicThetaLocalEnergyJet (cubicThetaTestLocalization φ F) y‖^2 := by
    rw [cubicTheta_l2_norm_sq_measure]
    apply integral_congr_ae
    filter_upwards [(cubicThetaLocalSectionJet_memLp hφ hc hp F).coeFn_toLp] with y hy
    change ‖((cubicThetaLocalSectionJet_memLp hφ hc hp F).toLp _) y‖^2=_
    rw [hy]
  rw [hn]
  exact h

end CubicFirstMoment.LocalSobolev

end

end OAI
