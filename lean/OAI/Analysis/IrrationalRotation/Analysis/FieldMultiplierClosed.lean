import OAI.Analysis.IrrationalRotation.Analysis.FieldMultiplierAdjoint

namespace OAI

noncomputable section
open MeasureTheory Filter
namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem fieldUnboundedMultiplier_congr_ae {h g : X → ℤ → ℂ}
    (hhg : ∀ᵐ x ∂μ, ∀ k, h x k = g x k) :
    fieldUnboundedMultiplier μ h = fieldUnboundedMultiplier μ g := by
  apply LinearPMap.eq_of_eq_graph
  rw [fieldUnboundedMultiplier_graph, fieldUnboundedMultiplier_graph]
  ext p
  constructor
  · intro hp
    filter_upwards [hp, hhg] with x hp hx
    intro k
    rw [← hx k]
    exact hp k
  · intro hp
    filter_upwards [hp, hhg] with x hp hx
    intro k
    rw [hx k]
    exact hp k

theorem fieldUnboundedMultiplier_isClosed (h : X → ℤ → ℂ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) :
    (fieldUnboundedMultiplier μ h).IsClosed := by
  have hc := LinearPMap.adjoint_isClosed
    (dense_fieldUnboundedMultiplier_domain (fun x k => star (h x k))
      (fun k => (hm k).star))
  rw [adjoint_fieldUnboundedMultiplier (fun x k => star (h x k))
    (fun k => (hm k).star)] at hc
  simpa only [star_star] using hc

theorem isClosed_fieldMultiplierGraph (h : X → ℤ → ℂ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) :
    IsClosed (fieldMultiplierGraph μ h : Set (FieldHilbert μ × FieldHilbert μ)) := by
  have hc := fieldUnboundedMultiplier_isClosed h hm
  rw [LinearPMap.IsClosed, fieldUnboundedMultiplier_graph] at hc
  exact hc

end Invariant233.WeightedShift

end

end OAI
