import OAI.Analysis.IrrationalRotation.Operators.NormalTracialTransport
import OAI.Analysis.IrrationalRotation.Analysis.VonNeumannSupportGeometry

namespace OAI

noncomputable section

namespace Invariant233.NormalTracialMeet

open NormalTracialTransport

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem extendedTrace_support_eq (M : VonNeumannAlgebra H) (τ : TracialState M)
    (hτ : IsNormalFaithfulTracialState M τ) (A : H →L[ℂ] H) (hA : A ∈ M) :
    extendedTrace M τ A.kerᗮ.starProjection =
      extendedTrace M τ A.range.topologicalClosure.starProjection := by
  rw [Submodule.starProjection_orthogonal',
    VonNeumannSupportGeometry.range_closure_projection_eq, map_sub, map_sub]
  congr 1
  exact extendedTrace_kernel_eq_adjoint_kernel M τ hτ A hA

theorem trace_support_eq (M : VonNeumannAlgebra H) (τ : TracialState M)
    (hτ : IsNormalFaithfulTracialState M τ) (A : H →L[ℂ] H) (hA : A ∈ M) :
    τ ⟨A.kerᗮ.starProjection,
      VonNeumannSupportGeometry.kernel_orthogonal_projection_mem M A hA⟩ =
    τ ⟨A.range.topologicalClosure.starProjection,
      VonNeumannSupportGeometry.range_closure_projection_mem M A hA⟩ := by
  simpa only [extendedTrace_apply M τ _
      (VonNeumannSupportGeometry.kernel_orthogonal_projection_mem M A hA),
    extendedTrace_apply M τ _
      (VonNeumannSupportGeometry.range_closure_projection_mem M A hA)] using
    extendedTrace_support_eq M τ hτ A hA

private instance inf_complete (p q : Submodule ℂ H)
    [CompleteSpace p] [CompleteSpace q] : CompleteSpace ↥(p ⊓ q) := by
  have hp : IsClosed (p : Set H) :=
    (completeSpace_coe_iff_isComplete.mp inferInstance).isClosed
  have hq : IsClosed (q : Set H) :=
    (completeSpace_coe_iff_isComplete.mp inferInstance).isClosed
  exact (hp.inter hq).completeSpace_coe

theorem extendedTrace_meet_lower_bound
    (M : VonNeumannAlgebra H) (τ : TracialState M)
    (hτ : IsNormalFaithfulTracialState M τ)
    (p q : Submodule ℂ H) [CompleteSpace p] [CompleteSpace q]
    (hp : p.starProjection ∈ M) (hq : q.starProjection ∈ M) :
    (extendedTrace M τ p.starProjection).re +
      (extendedTrace M τ q.starProjection).re - 1 ≤
      (extendedTrace M τ (p ⊓ q).starProjection).re := by
  let A := (1 - q.starProjection) * p.starProjection
  have hA : A ∈ M := mul_mem (sub_mem (one_mem M) hq) hp
  have hqperp : qᗮ.starProjection ∈ M := by
    rw [Submodule.starProjection_orthogonal']
    exact sub_mem (one_mem M) hq
  have hmono := extendedTrace_projection_mono M τ
    A.range.topologicalClosure qᗮ
    (VonNeumannSupportGeometry.range_closure_projection_mem M A hA) hqperp
    (VonNeumannSupportGeometry.range_closure_complement_projection_le p q)
  rw [← extendedTrace_support_eq M τ hτ A hA] at hmono
  change (extendedTrace M τ
    (((1 - q.starProjection) * p.starProjection).kerᗮ.starProjection)).re ≤ _ at hmono
  rw [VonNeumannSupportGeometry.initial_support_complement_projection,
    map_sub, Complex.sub_re, extendedTrace_orthogonal, Complex.sub_re,
    Complex.one_re] at hmono
  linarith

theorem trace_meet_lower_bound
    (M : VonNeumannAlgebra H) (τ : TracialState M)
    (hτ : IsNormalFaithfulTracialState M τ)
    (p q : Submodule ℂ H) [CompleteSpace p] [CompleteSpace q]
    (hp : p.starProjection ∈ M) (hq : q.starProjection ∈ M) :
    (τ ⟨p.starProjection, hp⟩).re + (τ ⟨q.starProjection, hq⟩).re - 1 ≤
      (τ ⟨(p ⊓ q).starProjection,
        VonNeumannSupportGeometry.inf_projection_mem p q M hp hq⟩).re := by
  simpa only [extendedTrace_apply M τ _ hp, extendedTrace_apply M τ _ hq,
    extendedTrace_apply M τ _
      (VonNeumannSupportGeometry.inf_projection_mem p q M hp hq)] using
    extendedTrace_meet_lower_bound M τ hτ p q hp hq

end Invariant233.NormalTracialMeet

end

end OAI
