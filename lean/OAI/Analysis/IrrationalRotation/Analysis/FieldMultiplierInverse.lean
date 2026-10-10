import OAI.Analysis.IrrationalRotation.Analysis.FieldUnboundedMultiplier

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.WeightedShift

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem inverse_fieldUnboundedMultiplier (h : X → ℤ → ℂ)
    (hh : ∀ᵐ x ∂μ, ∀ k, h x k ≠ 0) :
    (fieldUnboundedMultiplier μ h).inverse =
      fieldUnboundedMultiplier μ (fun x k => (h x k)⁻¹) := by
  apply LinearPMap.ext
  · rw [LinearPMap.inverse_domain, fieldMultiplier_range h hh]
  · intro ξ hξ hη
    have hk : (fieldUnboundedMultiplier μ h).toFun.ker = ⊥ :=
      LinearMap.ker_eq_bot.mpr (fieldUnboundedMultiplier_injective h hh)
    have hpartialker : (fieldUnboundedMultiplier μ h).ker = ⊥ := by
      simp [LinearPMap.ker, hk]
    exact LinearPMap.inverse_apply_eq hpartialker
      (x := ⟨fieldUnboundedMultiplier μ (fun x k => (h x k)⁻¹) ⟨ξ, hη⟩,
        inverseFieldMultiplier_mem_domain h hh ⟨ξ, hη⟩⟩)
      (y := ⟨ξ, hξ⟩) (fieldMultiplier_mul_inverse h hh ⟨ξ, hη⟩)

theorem inverse_exponential_fieldUnboundedMultiplier (b : X → ℤ → ℝ) :
    (fieldUnboundedMultiplier μ (fun x k => (Real.exp (b x k) : ℂ))).inverse =
      fieldUnboundedMultiplier μ (fun x k => (Real.exp (-b x k) : ℂ)) := by
  rw [inverse_fieldUnboundedMultiplier _
    (Eventually.of_forall fun x k => Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero (b x k)))]
  congr 1
  funext x k
  simp only [Real.exp_neg, Complex.ofReal_inv]

end Invariant233.WeightedShift

end

end OAI
