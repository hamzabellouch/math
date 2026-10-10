import OAI.Analysis.CircleDomains.Modulus.RegularCurveNormalStrip
import OAI.Analysis.CircleDomains.Sobolev.ComplexTangentFrame

namespace OAI

/-! An actual smooth local normal chart around each regular curve point. -/
open Set Function
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma exists_regular_curve_normal_chart {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ)
    (t : ℝ) (ht : deriv γ t ≠ 0) :
    ∃ e : OpenPartialHomeomorph (ℝ × ℝ) ℂ,
      (t,0) ∈ e.source ∧ (∀ p, e p = curveNormalStrip γ p) ∧
      ContDiff ℝ ∞ e ∧ ContDiffAt ℝ ∞ e.symm (γ t) := by
  let L : (ℝ × ℝ) ≃L[ℝ] ℂ :=
    ContinuousLinearEquiv.ofBijective (complexTangentFrame (deriv γ t))
      (LinearMap.ker_eq_bot.mpr (complexTangentFrame_bijective ht).1)
      (LinearMap.range_eq_top.mpr (complexTangentFrame_bijective ht).2)
  have hc := curveNormalStrip_contDiff hγ
  have hdf : fderiv ℝ (curveNormalStrip γ) (t,0) = (L : (ℝ × ℝ) →L[ℝ] ℂ) := by
    apply ContinuousLinearMap.ext
    intro v
    exact curveNormalStrip_fderiv hγ t v
  have hd : HasFDerivAt (curveNormalStrip γ) (L : (ℝ × ℝ) →L[ℝ] ℂ) (t,0) := by
    rw [← hdf]
    exact (hc.differentiable (by simp) (t,0)).hasFDerivAt
  let e := hc.contDiffAt.toOpenPartialHomeomorph (curveNormalStrip γ) hd (by simp)
  have he : ∀ p, e p = curveNormalStrip γ p := fun _ => rfl
  have hp : (t,0) ∈ e.source := hc.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp)
  refine ⟨e,hp,he,hc,?_⟩
  have hval : e (t,0) = γ t := by simp [he,curveNormalStrip]
  rw [← hval]
  apply e.contDiffAt_symm (e.map_source hp) (f₀' := L)
  · change HasFDerivAt (curveNormalStrip γ) _ (e.symm (e (t,0)))
    rw [e.left_inv hp]
    exact hd
  · change ContDiffAt ℝ ∞ (curveNormalStrip γ) (e.symm (e (t,0)))
    rw [e.left_inv hp]
    exact hc.contDiffAt

end CircleDomainRigidity

end

end OAI
