import OAI.Analysis.IrrationalRotation.Operators.AffiliatedTransport
import OAI.Analysis.IrrationalRotation.Analysis.FieldMultiplierAdjoint
import OAI.Analysis.IrrationalRotation.Model.Rotation

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.WeightedShift

open InvariantRotation.AffiliatedTransport
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem field_transported_invariant
    (h f g : X → ℤ → ℂ) (c : ℂ) (hc : c ≠ 0)
    (A B : FieldHilbert μ →L[ℂ] FieldHilbert μ)
    (hA : ∀ ξ, ∀ᵐ x ∂μ, ∀ k, A ξ x k = f x (k - 1) * ξ x (k - 1))
    (hB : ∀ ξ, ∀ᵐ x ∂μ, ∀ k, B ξ x k = g x (k - 1) * ξ x (k - 1))
    (hfg : ∀ᵐ x ∂μ, ∀ k, h x (k + 1) * f x k = c * g x k * h x k)
    (p : Submodule ℂ (FieldHilbert μ)) (hp : ∀ ξ ∈ p, A ξ ∈ p) :
    ∀ η ∈ transported (fieldUnboundedMultiplier μ h) p,
      B η ∈ transported (fieldUnboundedMultiplier μ h) p := by
  have hD : ∀ ξ ∈ (fieldUnboundedMultiplier μ h).domain,
      A ξ ∈ (fieldUnboundedMultiplier μ h).domain := by
    intro ξ hξ
    exact field_operator_mem_multiplierDomain h f g c A B hA hB hfg ⟨ξ, hξ⟩
  have hAB : ∀ ξ : (fieldUnboundedMultiplier μ h).domain,
      fieldUnboundedMultiplier μ h ⟨A ξ, hD ξ ξ.property⟩ =
        (c • B) (fieldUnboundedMultiplier μ h ξ) := by
    intro ξ
    exact field_multiplier_intertwines h f g c A B hA hB hfg ξ
  have hinv := transported_invariant (fieldUnboundedMultiplier μ h) p A (c • B)
    hp hD hAB
  intro η hη
  have hm := (transported (fieldUnboundedMultiplier μ h) p).smul_mem c⁻¹ (hinv η hη)
  simpa only [smul_apply, smul_smul, inv_mul_cancel₀ hc, one_smul] using hm

theorem field_transported_projection_invariant
    (h f g : X → ℤ → ℂ) (c : ℂ) (hc : c ≠ 0)
    (A B : FieldHilbert μ →L[ℂ] FieldHilbert μ)
    (hA : ∀ ξ, ∀ᵐ x ∂μ, ∀ k, A ξ x k = f x (k - 1) * ξ x (k - 1))
    (hB : ∀ ξ, ∀ᵐ x ∂μ, ∀ k, B ξ x k = g x (k - 1) * ξ x (k - 1))
    (hfg : ∀ᵐ x ∂μ, ∀ k, h x (k + 1) * f x k = c * g x k * h x k)
    (p : Submodule ℂ (FieldHilbert μ)) (hp : ∀ ξ ∈ p, A ξ ∈ p) :
    let P := (transported (fieldUnboundedMultiplier μ h) p).starProjection
    (1 - P) * B * P = 0 := by
  let S := transported (fieldUnboundedMultiplier μ h) p
  have hrange : S.starProjection.range ∈ Module.End.invtSubmodule B.toLinearMap := by
    rw [Submodule.range_starProjection]
    apply (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mpr
    exact field_transported_invariant h f g c hc A B hA hB hfg p hp
  have heq := (ContinuousLinearMap.IsIdempotentElem.range_mem_invtSubmodule_iff
    S.isIdempotentElem_starProjection).mp hrange
  change S.starProjection * B * S.starProjection = B * S.starProjection at heq
  change (1 - S.starProjection) * B * S.starProjection = 0
  rw [sub_mul, one_mul, sub_mul, heq, sub_self]

theorem field_exponential_inverse_transported_orthogonal
    (b : X → ℤ → ℝ) (hm : ∀ k, AEStronglyMeasurable (fun x => b x k) μ)
    (p : Submodule ℂ (FieldHilbert μ)) :
    transported (fieldUnboundedMultiplier μ
      (fun x k => (Real.exp (b x k) : ℂ))).inverse pᗮ ≤
      (transported (fieldUnboundedMultiplier μ
        (fun x k => (Real.exp (b x k) : ℂ))) p)ᗮ := by
  apply inverse_transported_le_orthogonal_of_selfAdjoint
  · exact isSelfAdjoint_fieldUnboundedMultiplier_real (fun x k => Real.exp (b x k))
      (fun k => Real.continuous_exp.comp_aestronglyMeasurable (hm k))
  · apply LinearMap.ker_eq_bot.mpr
    apply fieldUnboundedMultiplier_injective
    exact Filter.Eventually.of_forall fun x k =>
      Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero (b x k))

end Invariant233.WeightedShift

namespace Invariant233.Rotation

open InvariantRotation.AffiliatedTransport

theorem transport_weighted_coordinate_ae (θ : ℝ) (a : C(Circle, ℂ)) (ξ : Hilbert) :
    ∀ᵐ x ∂circleMeasure, ∀ k,
      weighted θ a ξ x k = a (action θ (k - 1) x) * ξ x (k - 1) := by
  have hd : ∀ᵐ x ∂circleMeasure, ∀ k,
      representation θ a ξ x k = a (action θ k x) * ξ x k := by
    exact WeightedShift.fieldDiagonal_coordinate_ae _ _ _ _ _ ξ
  have hu := (WeightedShift.shift 1).toLinearIsometry.toContinuousLinearMap.coeFn_compLpL
    (p := 2) (representation θ a ξ)
  filter_upwards [hd, hu] with x hd hu
  intro k
  change ((WeightedShift.shift 1).toLinearIsometry.toContinuousLinearMap.compLpL
    2 circleMeasure (representation θ a ξ)) x k = _
  rw [hu]
  exact hd (k - 1)

theorem weighted_transported_projection_invariant
    (θ : ℝ) (h : Circle → ℤ → ℂ) (a b : C(Circle, ℂ))
    (c : ℂ) (hc : c ≠ 0)
    (hfg : ∀ᵐ x ∂circleMeasure, ∀ k,
      h x (k + 1) * a (action θ k x) = c * b (action θ k x) * h x k)
    (p : Submodule ℂ Hilbert) (hp : ∀ ξ ∈ p, weighted θ a ξ ∈ p) :
    let P := (transported (WeightedShift.fieldUnboundedMultiplier circleMeasure h) p).starProjection
    (1 - P) * weighted θ b * P = 0 :=
  WeightedShift.field_transported_projection_invariant h
    (fun x k => a (action θ k x)) (fun x k => b (action θ k x)) c hc
    (weighted θ a) (weighted θ b)
    (transport_weighted_coordinate_ae θ a) (transport_weighted_coordinate_ae θ b)
    hfg p hp

end Invariant233.Rotation

end

end OAI
