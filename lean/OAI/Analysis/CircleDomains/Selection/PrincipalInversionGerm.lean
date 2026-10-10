import OAI.Analysis.CircleDomains.Selection.PrincipalExteriorGerm

namespace OAI

/-! The inversion conjugate of a principal holomorphic exterior map has
an analytic germ at zero with derivative one. -/
open Filter Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def principalInversionGerm (F : ℂ → ℂ) : ℂ → ℂ :=
  Function.update (fun w => (F w⁻¹)⁻¹) 0 0

lemma principalInversionGerm_eq (F : ℂ → ℂ) :
    principalInversionGerm F =
      fun w => w / (1 + w * invertedPrincipalRemainder F w) := by
  funext w
  by_cases hw : w = 0
  · subst w
    simp [principalInversionGerm]
  · simp only [principalInversionGerm, invertedPrincipalRemainder,
      Function.update_of_ne hw]
    have he : 1 + w * (F w⁻¹ - w⁻¹) = w * F w⁻¹ := by
      rw [mul_sub, mul_inv_cancel₀ hw]
      ring
    rw [he]
    simp only [div_eq_mul_inv, mul_inv_rev]
    calc
      _ = (w * w⁻¹) * (F w⁻¹)⁻¹ := by rw [mul_inv_cancel₀ hw, one_mul]
      _ = _ := by ring

lemma principalInversionGerm_analytic_deriv {F : ℂ → ℂ}
    (hF : ∀ᶠ z in Bornology.cobounded ℂ, DifferentiableAt ℂ F z)
    (ht : Tendsto (fun z => F z - z) (Bornology.cobounded ℂ) (𝓝 0)) :
    AnalyticAt ℂ (principalInversionGerm F) 0 ∧
      HasDerivAt (principalInversionGerm F) 1 0 := by
  have hR := invertedPrincipalRemainder_analytic hF ht
  have hden : 1 + (0 : ℂ) * invertedPrincipalRemainder F 0 ≠ 0 := by simp
  rw [principalInversionGerm_eq]
  constructor
  · exact analyticAt_id.div (analyticAt_const.add (analyticAt_id.mul hR)) hden
  · have hd := (hasDerivAt_id (0 : ℂ)).div
      ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).add ((hasDerivAt_id (0 : ℂ)).mul hR.differentiableAt.hasDerivAt)) hden
    convert hd using 1
    · funext w
      rfl
    · simp

end CircleDomainRigidity

end

end OAI
