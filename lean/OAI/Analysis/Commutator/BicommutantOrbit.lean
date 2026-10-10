import Mathlib

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def orbitSubmodule (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H) : Submodule ℂ H where
  carrier := {x | ∃ a : H →L[ℂ] H, a ∈ S ∧ a ξ = x}
  zero_mem' := ⟨0, S.zero_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, S.add_mem ha hb, rfl⟩
  smul_mem' := by
    rintro c x ⟨a, ha, rfl⟩
    exact ⟨c • a, S.smul_mem ha c, rfl⟩

def cyclicSubspace (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H) : Submodule ℂ H :=
  (orbitSubmodule S ξ).topologicalClosure

instance (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H) : IsClosed ((cyclicSubspace S ξ : Submodule ℂ H) : Set H) :=
  (orbitSubmodule S ξ).isClosed_topologicalClosure

lemma mem_cyclicSubspace_self (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H) :
    ξ ∈ cyclicSubspace S ξ := by
  exact (orbitSubmodule S ξ).le_topologicalClosure ⟨1, S.one_mem, by simp⟩

lemma cyclicSubspace_invariant (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H)
    {a : H →L[ℂ] H} (ha : a ∈ S) :
    ∀ x ∈ cyclicSubspace S ξ, a x ∈ cyclicSubspace S ξ := by
  intro x hx
  apply closure_minimal (t := {x | a x ∈ cyclicSubspace S ξ}) ?_ ?_ hx
  · rintro y ⟨b, hb, rfl⟩
    exact (orbitSubmodule S ξ).le_topologicalClosure
      ⟨a * b, S.mul_mem ha hb, rfl⟩
  · exact (orbitSubmodule S ξ).isClosed_topologicalClosure.preimage a.continuous

lemma projection_commutes_of_invariant (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    (a : H →L[ℂ] H)
    (ha : ∀ x ∈ P, a x ∈ P) (hstar : ∀ x ∈ P, (star a) x ∈ P) :
    P.starProjection * a = a * P.starProjection := by
  ext x
  change P.starProjection (a x) = a (P.starProjection x)
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ha _ (P.starProjection_apply_mem x)
  · intro w hw
    rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right]
    exact Submodule.starProjection_inner_eq_zero x _ (hstar w hw)

lemma cyclic_projection_mem_commutant (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H) :
    (cyclicSubspace S ξ).starProjection ∈ Set.centralizer (S : Set (H →L[ℂ] H)) := by
  intro a ha
  exact (projection_commutes_of_invariant (cyclicSubspace S ξ) a
    (cyclicSubspace_invariant S ξ ha) (cyclicSubspace_invariant S ξ (star_mem ha))).symm

theorem bicommutant_mem_cyclicSubspace (S : StarSubalgebra ℂ (H →L[ℂ] H))
    {T : H →L[ℂ] H} (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (ξ : H) : T ξ ∈ cyclicSubspace S ξ := by
  apply Submodule.starProjection_eq_self_iff.mp
  have h := congrArg (fun R : H →L[ℂ] H => R ξ)
    (hT _ (cyclic_projection_mem_commutant S ξ))
  simpa only [mul_apply_eq_comp,
    Submodule.starProjection_eq_self_iff.mpr (mem_cyclicSubspace_self S ξ)] using h

end Kadison
end

end OAI
