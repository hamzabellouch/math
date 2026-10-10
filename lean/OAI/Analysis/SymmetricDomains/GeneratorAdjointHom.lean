import Mathlib
import OAI.Analysis.SymmetricDomains.GeneratorPushForwardLinear

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U)
include hU

theorem pushForwardGenerator_mul (q r : Biholomorph U U) (X : Affine n → Affine n) :
    pushForwardGenerator (q*r) X=pushForwardGenerator q (pushForwardGenerator r X) := by
  funext x
  by_cases hx : x∈U
  · rw [pushForwardGenerator_apply (q*r) X ⟨x,hx⟩,
      pushForwardGenerator_apply q (pushForwardGenerator r X) ⟨x,hx⟩]
    rw [pushForwardGenerator_apply,derivativeAt_mul hU]
    have he : (q*r).toHomeomorph.symm ⟨x,hx⟩=
        r.toHomeomorph.symm (q.toHomeomorph.symm ⟨x,hx⟩) := rfl
    rw [he,Homeomorph.apply_symm_apply]
    rfl
  · simp only [pushForwardGenerator,dite_eq_right hx]

theorem pushForwardGenerator_one {X : Affine n → Affine n} (hX : ∀ x∉U, X x=0) :
    pushForwardGenerator (1 : Biholomorph U U) X=X := by
  funext x
  by_cases hx : x∈U
  · rw [pushForwardGenerator_apply (1 : Biholomorph U U) X ⟨x,hx⟩]
    change (1 : Biholomorph U U).derivativeAt ⟨x,hx⟩ (X x)=X x
    rw [derivativeAt_one hU]
    rfl
  · simp only [pushForwardGenerator,dite_eq_right hx,hX x hx]

variable [LocallyCompactSpace U] (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))

def generatorAdjoint (q : Biholomorph U U) :
    completeGeneratorSpace hU hc hbd Γ hhol ≃ₗ[ℝ] completeGeneratorSpace hU hc hbd Γ hhol where
  toLinearMap := generatorPushForwardLinear hU hc hbd Γ hhol q
  invFun := generatorPushForwardLinear hU hc hbd Γ hhol q⁻¹
  left_inv X := by
    apply Subtype.ext
    change pushForwardGenerator q⁻¹ (pushForwardGenerator q X.val)=X.val
    rw [← pushForwardGenerator_mul hU,inv_mul_cancel]
    exact pushForwardGenerator_one hU (fun _ hx => X.property.eq_zero_of_not_mem hx)
  right_inv X := by
    apply Subtype.ext
    change pushForwardGenerator q (pushForwardGenerator q⁻¹ X.val)=X.val
    rw [← pushForwardGenerator_mul hU,mul_inv_cancel]
    exact pushForwardGenerator_one hU (fun _ hx => X.property.eq_zero_of_not_mem hx)

def generatorAdjointHom : Biholomorph U U →*
    (completeGeneratorSpace hU hc hbd Γ hhol ≃ₗ[ℝ] completeGeneratorSpace hU hc hbd Γ hhol) where
  toFun := generatorAdjoint hU hc hbd Γ hhol
  map_one' := by
    apply LinearEquiv.ext
    intro X
    apply Subtype.ext
    exact pushForwardGenerator_one hU (fun _ hx => X.property.eq_zero_of_not_mem hx)
  map_mul' q r := by
    apply LinearEquiv.ext
    intro X
    apply Subtype.ext
    exact pushForwardGenerator_mul hU q r X.val
end Biholomorph
end Release061

end

end OAI
