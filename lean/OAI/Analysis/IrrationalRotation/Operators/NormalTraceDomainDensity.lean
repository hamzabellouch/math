import OAI.Analysis.IrrationalRotation.Operators.NormalTracialTransport
import OAI.Analysis.IrrationalRotation.Spectral.AffiliatedPositiveResolvent
import OAI.Analysis.IrrationalRotation.Spectral.PartialResolventCalculus

namespace OAI

noncomputable section
namespace Invariant233.NormalTraceDomainDensity

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open NormalTracialTransport BoundedRangeTrace

theorem eq_of_le_of_trace_eq
    (M : VonNeumannAlgebra E) (τ : TracialState M)
    (hτ : IsNormalFaithfulTracialState M τ)
    (p q : Submodule ℂ E) [CompleteSpace p] [CompleteSpace q]
    (hp : p.starProjection ∈ M) (hq : q.starProjection ∈ M)
    (hpq : p ≤ q)
    (heq : extendedTrace M τ p.starProjection = extendedTrace M τ q.starProjection) :
    p = q := by
  have hproj : IsStarProjection (q.starProjection - p.starProjection) :=
    isStarProjection_starProjection.sub_of_mul_eq_left isStarProjection_starProjection
      (Submodule.starProjection_comp_starProjection_of_le hpq)
  have hmem : q.starProjection - p.starProjection ∈ M := sub_mem hq hp
  have hz : τ ⟨q.starProjection - p.starProjection, hmem⟩ = 0 := by
    rw [← extendedTrace_apply M τ _ hmem, map_sub, heq, sub_self]
  have hzero := hτ.1 ⟨q.starProjection - p.starProjection, hmem⟩
    (ContinuousLinearMap.IsPositive.of_isStarProjection hproj) hz
  have hpzero : q.starProjection - p.starProjection = 0 := congrArg Subtype.val hzero
  have hprojection : q.starProjection = p.starProjection := sub_eq_zero.mp hpzero
  have hrange := congrArg (fun A : E →L[ℂ] E => A.range) hprojection
  simpa only [Submodule.range_starProjection] using hrange.symm

theorem closure_inf_eq_of_normalizer
    (M : VonNeumannAlgebra E) (τ : TracialState M)
    (hτ : IsNormalFaithfulTracialState M τ)
    (A : E →L[ℂ] E) (hA : A ∈ M)
    (hinj : Function.Injective A) (hadj : Function.Injective A.adjoint)
    (d p : Submodule ℂ E) [CompleteSpace p]
    (hD : A.range ≤ d) (hp : p.starProjection ∈ M) :
    (p ⊓ d).topologicalClosure = p := by
  let r := ((1 - p.starProjection) * A).ker
  have hr : r.starProjection ∈ M := kernel_projection_mem M _
    (mul_mem (sub_mem (one_mem M) hp) hA)
  let q := (A * r.starProjection).range.topologicalClosure
  let : IsClosed (q : Set E) := Submodule.isClosed_topologicalClosure _
  let : CompleteSpace q := inferInstance
  have hq : q.starProjection ∈ M := range_closure_projection_mem M _ (mul_mem hA hr)
  have hrange : (A * r.starProjection).range ≤ p ⊓ d := by
    rintro y ⟨x, rfl⟩
    constructor
    · have hx := r.starProjection_apply_mem x
      change A (r.starProjection x) - p.starProjection (A (r.starProjection x)) = 0 at hx
      exact p.starProjection_eq_self_iff.mp (sub_eq_zero.mp hx).symm
    · exact hD ⟨r.starProjection x, rfl⟩
  have hqp : q ≤ p := by
    apply Submodule.topologicalClosure_minimal _ (hrange.trans inf_le_left)
    exact (completeSpace_coe_iff_isComplete.mp inferInstance).isClosed
  have htrace : extendedTrace M τ q.starProjection = extendedTrace M τ p.starProjection := by
    exact (extendedTrace_range_eq_of_injective M τ hτ A hA hinj r hr).trans
      (extendedTrace_preimage_eq M τ hτ A hA hadj p hp)
  have hqeq : q = p := eq_of_le_of_trace_eq M τ hτ q p hq hp hqp htrace
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal _ inf_le_left
    exact (completeSpace_coe_iff_isComplete.mp inferInstance).isClosed
  · calc
      p = q := hqeq.symm
      _ ≤ (p ⊓ d).topologicalClosure := Submodule.topologicalClosure_mono hrange

theorem closure_inf_domain_eq_of_normalizer
    (M : VonNeumannAlgebra E) (τ : TracialState M)
    (hτ : IsNormalFaithfulTracialState M τ)
    (H : E →ₗ.[ℂ] E) (A : E →L[ℂ] E) (hA : A ∈ M)
    (hinj : Function.Injective A) (hadj : Function.Injective A.adjoint)
    (hD : ∀ x, A x ∈ H.domain)
    (p : Submodule ℂ E) [CompleteSpace p] (hp : p.starProjection ∈ M) :
    (p ⊓ H.domain).topologicalClosure = p := by
  apply closure_inf_eq_of_normalizer M τ hτ A hA hinj hadj H.domain p _ hp
  rintro y ⟨x, rfl⟩
  exact hD x

theorem closure_inf_domain_eq_of_affiliated
    (M : VonNeumannAlgebra E) (τ : TracialState M)
    (hτ : IsNormalFaithfulTracialState M τ)
    (H : E →ₗ.[ℂ] E) (hH : IsSelfAdjoint H)
    (hpos : IsPositivePartial H) (haff : IsAffiliated M H)
    (p : Submodule ℂ E) [CompleteSpace p] (hp : p.starProjection ∈ M) :
    (p ⊓ H.domain).topologicalClosure = p := by
  obtain ⟨R, hRM, _, hD, hHR, _, _⟩ :=
    PositivePartialResolvent.exists_affiliated_resolvent M H hH hpos haff
  have hHR' : ∀ x : E, H ⟨R x, hD x⟩ = x - R x := fun x => hHR x (hD x)
  have hinj : Function.Injective R := PartialResolvent.injective H R hD hHR'
  have hformal : H.IsFormalAdjoint H := by
    have hh := LinearPMap.adjoint_isFormalAdjoint hH.dense_domain
    rwa [LinearPMap.isSelfAdjoint_def.mp hH] at hh
  have hRself := PartialResolvent.isSelfAdjoint H R hD hHR' hformal
  have hadj : Function.Injective R.adjoint := by
    rw [← ContinuousLinearMap.star_eq_adjoint, hRself.star_eq]
    exact hinj
  exact closure_inf_domain_eq_of_normalizer M τ hτ H R hRM hinj hadj hD p hp

end Invariant233.NormalTraceDomainDensity

end

end OAI
