import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalAnalytic
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRobinRegularity

namespace OAI

/-! Value and radial-derivative traces of the two-component physical jet. -/

open Filter Topology
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def spectralPhysicalValueMap : E₄ →L[ℂ] ℂ × ℂ :=
  ((ContinuousLinearMap.fst ℂ ℂ ℂ).comp (ContinuousLinearMap.fst ℂ (ℂ × ℂ) (ℂ × ℂ))).prod
    ((ContinuousLinearMap.fst ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ (ℂ × ℂ) (ℂ × ℂ)))

noncomputable def spectralPhysicalDerivativeMap : E₄ →L[ℂ] ℂ × ℂ :=
  ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp (ContinuousLinearMap.fst ℂ (ℂ × ℂ) (ℂ × ℂ))).prod
    ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ (ℂ × ℂ) (ℂ × ℂ)))

theorem spectralPhysicalValueMap_pair (νp νm : ℂ) (Y : ℝ → E₄) (r : ℝ) :
    spectralPhysicalValueMap (spectralPhysicalPair νp νm Y r)=
      (Complex.exp (νp*(Real.log r : ℂ))*(Y (Real.log r)).1.1,
       Complex.exp (νm*(Real.log r : ℂ))*(Y (Real.log r)).2.1) := rfl

theorem spectralPhysicalValueDet_factor (νp νm : ℂ) (Yp Ym : ℝ → E₄) (r : ℝ) :
    spectralValueDet (spectralPhysicalValueMap (spectralPhysicalPair νp νm Yp r))
      (spectralPhysicalValueMap (spectralPhysicalPair νp νm Ym r))=
      Complex.exp (νp*(Real.log r : ℂ))*Complex.exp (νm*(Real.log r : ℂ))*
        spectralValueDet ((Yp (Real.log r)).1.1,(Yp (Real.log r)).2.1)
          ((Ym (Real.log r)).1.1,(Ym (Real.log r)).2.1) := by
  rw [spectralPhysicalValueMap_pair,spectralPhysicalValueMap_pair]
  dsimp only [spectralValueDet]
  ring

theorem spectralPhysicalValueDet_eventually_ne_zero (νp νm : ℂ) (Yp Ym : ℝ → E₄)
    (hp : Tendsto Yp atTop (𝓝 ((1,0),(0,0))))
    (hm : Tendsto Ym atTop (𝓝 ((0,0),(1,0)))) :
    ∀ᶠ r in atTop,
      spectralValueDet (spectralPhysicalValueMap (spectralPhysicalPair νp νm Yp r))
        (spectralPhysicalValueMap (spectralPhysicalPair νp νm Ym r)) ≠ 0 := by
  have hd : Tendsto (fun t => spectralValueDet ((Yp t).1.1,(Yp t).2.1)
      ((Ym t).1.1,(Ym t).2.1)) atTop (𝓝 1) := by
    simpa only [spectralValueDet,one_mul,zero_mul,sub_zero] using
      (hp.fst_nhds.fst_nhds.mul hm.snd_nhds.fst_nhds).sub
        (hp.snd_nhds.fst_nhds.mul hm.fst_nhds.fst_nhds)
  have hn := hd.eventually (eventually_ne_nhds (by norm_num : (1 : ℂ) ≠ 0))
  filter_upwards [Real.tendsto_log_atTop.eventually hn] with r hr
  rw [spectralPhysicalValueDet_factor]
  exact mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)) hr

end DefocusingNLS

end OAI
