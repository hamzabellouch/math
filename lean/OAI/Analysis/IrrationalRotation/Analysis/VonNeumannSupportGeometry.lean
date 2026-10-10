import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

namespace OAI

noncomputable section

namespace Invariant233.VonNeumannSupportGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem kernel_projection_mem (M : VonNeumannAlgebra H) (a : H →L[ℂ] H)
    (ha : a ∈ M) : a.ker.starProjection ∈ M := by
  apply (VonNeumannAlgebra.IsStarProjection.mem_iff
    isStarProjection_starProjection M).mpr
  intro w hw
  rw [Submodule.range_starProjection]
  apply (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mpr
  intro x hx
  change a (w x) = 0
  have hc := congrArg (fun b : H →L[ℂ] H => b x)
    ((VonNeumannAlgebra.mem_commutant_iff.mp hw) a ha)
  change a (w x) = w (a x) at hc
  rw [hc, show a x = 0 from hx, map_zero]

theorem range_closure_projection_mem (M : VonNeumannAlgebra H)
    (a : H →L[ℂ] H) (ha : a ∈ M) :
    a.range.topologicalClosure.starProjection ∈ M := by
  apply (VonNeumannAlgebra.IsStarProjection.mem_iff
    isStarProjection_starProjection M).mpr
  intro w hw
  rw [Submodule.range_starProjection]
  apply Submodule.topologicalClosure_mem_invtSubmodule
  apply (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mpr
  rintro y ⟨x, rfl⟩
  refine ⟨w x, ?_⟩
  exact congrArg (fun b : H →L[ℂ] H => b x)
    ((VonNeumannAlgebra.mem_commutant_iff.mp hw) a ha)

theorem kernel_orthogonal_projection_mem (M : VonNeumannAlgebra H)
    (a : H →L[ℂ] H) (ha : a ∈ M) : a.kerᗮ.starProjection ∈ M := by
  rw [Submodule.starProjection_orthogonal']
  exact sub_mem (one_mem M) (kernel_projection_mem M a ha)

theorem range_closure_projection_eq (a : H →L[ℂ] H) :
    a.range.topologicalClosure.starProjection =
      1 - (star a).ker.starProjection := by
  rw [← Submodule.starProjection_orthogonal']
  congr 1
  simpa only [ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_adjoint] using
    (ContinuousLinearMap.orthogonal_ker (star a)).symm

section Meet

variable (p q : Submodule ℂ H) [p.HasOrthogonalProjection] [q.HasOrthogonalProjection]

private theorem inf_hasOrthogonalProjection : (p ⊓ q).HasOrthogonalProjection := by
  have hp : IsClosed (p : Set H) := by
    rw [← p.orthogonal_orthogonal]
    exact pᗮ.isClosed_orthogonal
  have hq : IsClosed (q : Set H) := by
    rw [← q.orthogonal_orthogonal]
    exact qᗮ.isClosed_orthogonal
  let : IsClosed ((p ⊓ q : Submodule ℂ H) : Set H) := hp.inter hq
  infer_instance

local instance : (p ⊓ q).HasOrthogonalProjection := inf_hasOrthogonalProjection p q

theorem inf_projection_mem (M : VonNeumannAlgebra H)
    (hp : p.starProjection ∈ M) (hq : q.starProjection ∈ M) :
    (p ⊓ q).starProjection ∈ M := by
  apply (VonNeumannAlgebra.IsStarProjection.mem_iff
    isStarProjection_starProjection M).mpr
  intro w hw
  rw [Submodule.range_starProjection]
  apply (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mpr
  have hpi := (VonNeumannAlgebra.IsStarProjection.mem_iff
    isStarProjection_starProjection M).mp hp w hw
  have hqi := (VonNeumannAlgebra.IsStarProjection.mem_iff
    isStarProjection_starProjection M).mp hq w hw
  rw [Submodule.range_starProjection] at hpi hqi
  intro x hx
  exact ⟨(Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mp hpi x hx.1,
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mp hqi x hx.2⟩

omit [CompleteSpace H] in

theorem inf_kernel_complement_projection :
    p ⊓ ((1 - q.starProjection) * p.starProjection).ker = p ⊓ q := by
  ext x
  constructor
  · rintro ⟨hp, hx⟩
    refine ⟨hp, ?_⟩
    change p.starProjection x - q.starProjection (p.starProjection x) = 0 at hx
    rw [Submodule.starProjection_eq_self_iff.mpr hp] at hx
    exact Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hx).symm
  · rintro ⟨hp, hq⟩
    refine ⟨hp, ?_⟩
    change p.starProjection x - q.starProjection (p.starProjection x) = 0
    rw [Submodule.starProjection_eq_self_iff.mpr hp,
      Submodule.starProjection_eq_self_iff.mpr hq, sub_self]

omit [CompleteSpace H] in

theorem kernel_complement_projection :
    ((1 - q.starProjection) * p.starProjection).ker = pᗮ ⊔ (p ⊓ q) := by
  ext x
  constructor
  · intro hx
    change p.starProjection x - q.starProjection (p.starProjection x) = 0 at hx
    apply Submodule.mem_sup.mpr
    refine ⟨x - p.starProjection x, p.sub_starProjection_mem_orthogonal x,
      p.starProjection x, ⟨p.starProjection_apply_mem x, ?_⟩, sub_add_cancel x _⟩
    exact Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hx).symm
  · intro hx
    obtain ⟨u, hu, v, ⟨hvp, hvq⟩, rfl⟩ := Submodule.mem_sup.mp hx
    have hu0 : p.starProjection u = 0 := by
      change u ∈ p.starProjection.ker
      rwa [Submodule.ker_starProjection]
    change p.starProjection (u + v) - q.starProjection (p.starProjection (u + v)) = 0
    rw [map_add, hu0, zero_add, Submodule.starProjection_eq_self_iff.mpr hvp,
      Submodule.starProjection_eq_self_iff.mpr hvq, sub_self]

theorem initial_support_complement_projection :
    ((1 - q.starProjection) * p.starProjection).kerᗮ.starProjection =
      p.starProjection - (p ⊓ q).starProjection := by
  let r : Submodule ℂ H := p ⊓ q
  have hrp : r ≤ p := inf_le_left
  have hrq : r ≤ q := inf_le_right
  have hk : ((1 - q.starProjection) * p.starProjection).ker = pᗮ ⊔ r :=
    kernel_complement_projection p q
  ext x
  change _ = p.starProjection x - r.starProjection x
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · rw [hk, ← Submodule.inf_orthogonal, p.orthogonal_orthogonal]
    refine ⟨p.sub_mem (p.starProjection_apply_mem x)
      (hrp (r.starProjection_apply_mem x)), ?_⟩
    rw [← Submodule.ker_starProjection]
    change r.starProjection (p.starProjection x - r.starProjection x) = 0
    have hc := congrArg (fun b : H →L[ℂ] H => b x)
      (Submodule.starProjection_comp_starProjection_of_le hrp)
    change r.starProjection (p.starProjection x) = r.starProjection x at hc
    rw [map_sub, hc,
      Submodule.starProjection_eq_self_iff.mpr (r.starProjection_apply_mem x), sub_self]
  · rw [Submodule.orthogonal_orthogonal, hk]
    apply Submodule.mem_sup.mpr
    refine ⟨x - p.starProjection x, p.sub_starProjection_mem_orthogonal x,
      r.starProjection x, r.starProjection_apply_mem x, ?_⟩
    abel

omit [CompleteSpace H] in

theorem range_closure_complement_projection_le :
    ((1 - q.starProjection) * p.starProjection).range.topologicalClosure ≤ qᗮ := by
  apply Submodule.topologicalClosure_minimal _ _ q.isClosed_orthogonal
  rintro y ⟨x, rfl⟩
  exact q.sub_starProjection_mem_orthogonal (p.starProjection x)

end Meet

end Invariant233.VonNeumannSupportGeometry

end

end OAI
