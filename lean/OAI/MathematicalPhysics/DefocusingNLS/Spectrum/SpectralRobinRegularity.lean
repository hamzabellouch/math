import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRobinMatrix

namespace OAI

/-! Continuity and holomorphy of the exact outgoing Robin matrix, on the
open set where the value columns are invertible. -/

open Filter Topology
namespace DefocusingNLS

theorem spectralValueDet_tendsto (u v : ℕ → ℂ × ℂ) (u₀ v₀ : ℂ × ℂ)
    (hu : Tendsto u atTop (𝓝 u₀)) (hv : Tendsto v atTop (𝓝 v₀)) :
    Tendsto (fun n => spectralValueDet (u n) (v n)) atTop (𝓝 (spectralValueDet u₀ v₀)) :=
  (hu.fst_nhds.mul hv.snd_nhds).sub (hu.snd_nhds.mul hv.fst_nhds)

theorem spectralValueInverse_tendsto (u v : ℕ → ℂ × ℂ) (u₀ v₀ : ℂ × ℂ)
    (hu : Tendsto u atTop (𝓝 u₀)) (hv : Tendsto v atTop (𝓝 v₀))
    (h : spectralValueDet u₀ v₀ ≠ 0) :
    Tendsto (fun n => spectralValueInverse (u n) (v n)) atTop
      (𝓝 (spectralValueInverse u₀ v₀)) := by
  have hc := spectralTwoColumns_tendsto
    (fun n => ((v n).2,-(u n).2)) (fun n => (-(v n).1,(u n).1))
    (v₀.2,-u₀.2) (-v₀.1,u₀.1)
    (hv.snd_nhds.prodMk_nhds hu.snd_nhds.neg) (hv.fst_nhds.neg.prodMk_nhds hu.fst_nhds)
  exact ((spectralValueDet_tendsto u v u₀ v₀ hu hv).inv₀ h).smul hc

theorem spectralRobinOperator_tendsto (u v du dv : ℕ → ℂ × ℂ) (u₀ v₀ du₀ dv₀ : ℂ × ℂ)
    (hu : Tendsto u atTop (𝓝 u₀)) (hv : Tendsto v atTop (𝓝 v₀))
    (hdu : Tendsto du atTop (𝓝 du₀)) (hdv : Tendsto dv atTop (𝓝 dv₀))
    (h : spectralValueDet u₀ v₀ ≠ 0) :
    Tendsto (fun n => spectralRobinOperator (u n) (v n) (du n) (dv n)) atTop
      (𝓝 (spectralRobinOperator u₀ v₀ du₀ dv₀)) :=
  spectralComposition_tendsto _ _ _ _
    (spectralTwoColumns_tendsto du dv du₀ dv₀ hdu hdv)
    (spectralValueInverse_tendsto u v u₀ v₀ hu hv h)

theorem spectralValueInverse_analyticAt (u v : ℂ → ℂ × ℂ) (z : ℂ)
    (hu : AnalyticAt ℂ u z) (hv : AnalyticAt ℂ v z)
    (h : spectralValueDet (u z) (v z) ≠ 0) :
    AnalyticAt ℂ (fun w => spectralValueInverse (u w) (v w)) z := by
  have hu₁ : AnalyticAt ℂ (fun w => (u w).1) z :=
    ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt (u z)).comp hu
  have hu₂ : AnalyticAt ℂ (fun w => (u w).2) z :=
    ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt (u z)).comp hu
  have hv₁ : AnalyticAt ℂ (fun w => (v w).1) z :=
    ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt (v z)).comp hv
  have hv₂ : AnalyticAt ℂ (fun w => (v w).2) z :=
    ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt (v z)).comp hv
  have hd : AnalyticAt ℂ (fun w => spectralValueDet (u w) (v w)) z :=
    (hu₁.mul hv₂).sub (hu₂.mul hv₁)
  have hc := spectralTwoColumns_analyticAt
    (fun w => ((v w).2,-(u w).2)) (fun w => (-(v w).1,(u w).1)) z
    (hv₂.prod hu₂.neg) (hv₁.neg.prod hu₁)
  exact (hd.inv h).smul hc

theorem spectralRobinOperator_analyticAt (u v du dv : ℂ → ℂ × ℂ) (z : ℂ)
    (hu : AnalyticAt ℂ u z) (hv : AnalyticAt ℂ v z)
    (hdu : AnalyticAt ℂ du z) (hdv : AnalyticAt ℂ dv z)
    (h : spectralValueDet (u z) (v z) ≠ 0) :
    AnalyticAt ℂ (fun w => spectralRobinOperator (u w) (v w) (du w) (dv w)) z := by
  have hc := spectralTwoColumns_analyticAt du dv z hdu hdv
  have hi := spectralValueInverse_analyticAt u v z hu hv h
  exact ((ContinuousLinearMap.compL ℂ (ℂ × ℂ) (ℂ × ℂ) (ℂ × ℂ)).analyticAt_bilinear _).comp
    (hc.prod hi)

end DefocusingNLS

end OAI
