import OAI.Analysis.IrrationalRotation.Spectral.FieldResolvent
import OAI.Analysis.IrrationalRotation.Operators.AffiliatedTransportSupplement
import OAI.Analysis.IrrationalRotation.Model.AffiliatedTransport
import Mathlib.Analysis.VonNeumannAlgebra.Basic

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Invariant233.WeightedShift

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem closedImageOn_projection_mem_of_resolvent_mem
    (h : X → ℤ → ℝ) (hpos : ∀ x k, 0 ≤ h x k)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ)
    (M : VonNeumannAlgebra (FieldHilbert μ))
    (hR : positiveFieldResolvent h hpos hm ∈ M)
    (p : FieldHilbert μ →L[ℂ] FieldHilbert μ) (hp : p ∈ M) :
    (AffiliatedTransport.closedImageOn
      (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))) p.range).starProjection ∈ M := by
  apply (VonNeumannAlgebra.IsStarProjection.mem_iff
    isStarProjection_starProjection M).mpr
  intro A hA
  rw [Submodule.range_starProjection]
  have hAR : Commute A (positiveFieldResolvent h hpos hm) :=
    ((VonNeumannAlgebra.mem_commutant_iff.mp hA) _ hR).symm
  apply AffiliatedTransport.closedImageOn_invariant_of_commuting
    (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))) p.range A
    (fieldUnboundedMultiplier_domain_invariant_of_commute_resolvent h hpos hm A hAR)
    (fieldUnboundedMultiplier_commutes_of_commute_resolvent h hpos hm A hAR)
  rintro y ⟨z, rfl⟩
  refine ⟨A z, ?_⟩
  exact congrArg (fun B : FieldHilbert μ →L[ℂ] FieldHilbert μ => B z)
    ((VonNeumannAlgebra.mem_commutant_iff.mp hA) p hp)

theorem transported_projection_mem_of_resolvent_mem
    (h : X → ℤ → ℝ) (hpos : ∀ x k, 0 ≤ h x k)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ)
    (M : VonNeumannAlgebra (FieldHilbert μ))
    (hR : positiveFieldResolvent h hpos hm ∈ M)
    (p : FieldHilbert μ →L[ℂ] FieldHilbert μ) (hp : p ∈ M) :
    (InvariantRotation.AffiliatedTransport.transported
      (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))) p.range).starProjection ∈ M :=
  closedImageOn_projection_mem_of_resolvent_mem h hpos hm M hR p hp

theorem transported_projection_mem_and_invariant_of_resolvent_mem
    (h : X → ℤ → ℝ) (hpos : ∀ x k, 0 ≤ h x k)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ)
    (M : VonNeumannAlgebra (FieldHilbert μ))
    (hR : positiveFieldResolvent h hpos hm ∈ M)
    (p A B : FieldHilbert μ →L[ℂ] FieldHilbert μ) (hp : p ∈ M)
    (hAp : (1 - p) * A * p = 0)
    (hD : ∀ ξ : (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).domain,
      A ξ.val ∈ (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).domain)
    (hI : ∀ ξ : (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).domain,
      fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)) ⟨A ξ.val, hD ξ⟩ =
        B (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)) ξ)) :
    let P := (InvariantRotation.AffiliatedTransport.transported
      (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))) p.range).starProjection
    P ∈ M ∧ (1 - P) * B * P = 0 := by
  dsimp only
  refine ⟨transported_projection_mem_of_resolvent_mem h hpos hm M hR p hp, ?_⟩
  have hAp' : p * A * p = A * p := by
    rw [sub_mul, one_mul, sub_mul] at hAp
    exact (sub_eq_zero.mp hAp).symm
  have hrange : ∀ y ∈ p.range, A y ∈ p.range := by
    rintro y ⟨z, rfl⟩
    refine ⟨A (p z), ?_⟩
    exact congrArg (fun C : FieldHilbert μ →L[ℂ] FieldHilbert μ => C z) hAp'
  have hclosed := AffiliatedTransport.closedImageOn_invariant
    (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))) p.range A B hD hI hrange
  let S := InvariantRotation.AffiliatedTransport.transported
    (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))) p.range
  have hinv : S.starProjection.range ∈ Module.End.invtSubmodule B := by
    rw [Submodule.range_starProjection]
    exact hclosed
  have heq := (ContinuousLinearMap.IsIdempotentElem.range_mem_invtSubmodule_iff
    (isStarProjection_starProjection (U := S)).isIdempotentElem).mp hinv
  change S.starProjection * B * S.starProjection = B * S.starProjection at heq
  change (1 - S.starProjection) * B * S.starProjection = 0
  rw [sub_mul, one_mul, sub_mul, heq, sub_self]

end Invariant233.WeightedShift

end

end OAI
