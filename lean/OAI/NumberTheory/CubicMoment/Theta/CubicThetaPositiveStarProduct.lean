import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveLocalization

namespace OAI

/-! Compact conjugated test factors preserve integrability in the
positive-height chart. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaStar_support (φ : ℂ × ℝ → ℂ) :
    tsupport (fun p => star (φ p))⊆tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport φ)
  intro p hp
  apply subset_tsupport
  intro h
  exact hp (by simp [h])

lemma cubicThetaPositiveStarProduct_integrable {φ f : ℂ × ℝ → ℂ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hp : tsupport φ⊆{p : ℂ × ℝ | 0<p.2})
    (hf : ContinuousOn f {p : ℂ × ℝ | 0<p.2}) :
    Integrable (fun p => star (φ p)*f p) := by
  have hbar : Continuous (fun p => star (φ p)) := continuous_star.comp hφ
  have hcbar : HasCompactSupport (fun p => star (φ p)) :=
    hc.of_isClosed_subset isClosed_closure (cubicThetaStar_support φ)
  exact cubicThetaPositiveProduct_integrable hbar hcbar ((cubicThetaStar_support φ).trans hp) hf

end CubicFirstMoment

end

end OAI
