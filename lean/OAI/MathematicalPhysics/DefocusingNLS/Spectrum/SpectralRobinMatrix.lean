import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCompactPencil
import Mathlib.Analysis.Normed.Operator.Bilinear

namespace OAI

/-! The outgoing Robin operator obtained from two value/derivative columns.
Only the nonzero value determinant is needed for the local construction. -/

open Filter Topology
namespace DefocusingNLS

noncomputable def spectralTwoColumns (u v : ℂ × ℂ) : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
  (ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight u+
    (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight v

noncomputable def spectralValueDet (u v : ℂ × ℂ) : ℂ := u.1*v.2-u.2*v.1

noncomputable def spectralValueInverse (u v : ℂ × ℂ) : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
  (spectralValueDet u v)⁻¹ • spectralTwoColumns (v.2,-u.2) (-v.1,u.1)

noncomputable def spectralRobinOperator (u v du dv : ℂ × ℂ) : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
  (spectralTwoColumns du dv).comp (spectralValueInverse u v)

theorem spectralTwoColumns_apply (u v z : ℂ × ℂ) :
    spectralTwoColumns u v z=z.1 • u+z.2 • v := rfl

theorem spectralValueInverse_apply_columns (u v z : ℂ × ℂ)
    (h : spectralValueDet u v ≠ 0) :
    spectralValueInverse u v (spectralTwoColumns u v z)=z := by
  rcases u with ⟨a,c⟩
  rcases v with ⟨b,d⟩
  rcases z with ⟨x,y⟩
  change a*d-c*b ≠ 0 at h
  apply Prod.ext
  · change (a*d-c*b)⁻¹*((x*a+y*b)*d+(x*c+y*d)*(-b))=x
    field_simp [h]
    ring
  · change (a*d-c*b)⁻¹*((x*a+y*b)*(-c)+(x*c+y*d)*a)=y
    field_simp [h]
    ring

theorem spectralRobinOperator_columns (u v du dv z : ℂ × ℂ)
    (h : spectralValueDet u v ≠ 0) :
    spectralRobinOperator u v du dv (spectralTwoColumns u v z)=spectralTwoColumns du dv z := by
  rw [spectralRobinOperator,ContinuousLinearMap.comp_apply,spectralValueInverse_apply_columns u v z h]

theorem spectralTwoColumns_tendsto (u v : ℕ → ℂ × ℂ) (u₀ v₀ : ℂ × ℂ)
    (hu : Tendsto u atTop (𝓝 u₀)) (hv : Tendsto v atTop (𝓝 v₀)) :
    Tendsto (fun n => spectralTwoColumns (u n) (v n)) atTop (𝓝 (spectralTwoColumns u₀ v₀)) := by
  exact ((ContinuousLinearMap.smulRightL ℂ (ℂ × ℂ) (ℂ × ℂ)
    (ContinuousLinearMap.fst ℂ ℂ ℂ)).continuous.continuousAt.tendsto.comp hu).add
    ((ContinuousLinearMap.smulRightL ℂ (ℂ × ℂ) (ℂ × ℂ)
      (ContinuousLinearMap.snd ℂ ℂ ℂ)).continuous.continuousAt.tendsto.comp hv)

theorem spectralTwoColumns_analyticAt (u v : ℂ → ℂ × ℂ) (z : ℂ)
    (hu : AnalyticAt ℂ u z) (hv : AnalyticAt ℂ v z) :
    AnalyticAt ℂ (fun w => spectralTwoColumns (u w) (v w)) z := by
  exact (((ContinuousLinearMap.smulRightL ℂ (ℂ × ℂ) (ℂ × ℂ)
    (ContinuousLinearMap.fst ℂ ℂ ℂ)).analyticAt (u z)).comp hu).add
    (((ContinuousLinearMap.smulRightL ℂ (ℂ × ℂ) (ℂ × ℂ)
      (ContinuousLinearMap.snd ℂ ℂ ℂ)).analyticAt (v z)).comp hv)

end DefocusingNLS

end OAI
