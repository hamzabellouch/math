import Mathlib.LinearAlgebra.PID
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.Basic.Real.Basic

namespace OAI

/-! # Trace after removing a nilpotent quotient action

The Cartan ideal has the same adjoint trace as the ambient algebra because
the quotient action comes from the nilpotent Cartan algebra. This is the
finite-dimensional linear step of that argument.
-/

noncomputable section

namespace PolycyclicRecognition

variable {M : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]

theorem trace_eq_restrict_of_nilpotent_quotient
    (N : Submodule ℝ M) (f : M →ₗ[ℝ] M) (hf : ∀ x ∈ N, f x ∈ N)
    (hnil : IsNilpotent (N.mapQ N f hf)) :
    LinearMap.trace ℝ M f = LinearMap.trace ℝ N (f.restrict hf) := by
  let A := N.mapQ N f hf
  obtain ⟨s, hs⟩ := N.mkQ.exists_rightInverse_of_surjective N.range_mkQ
  have hsection (x : M ⧸ N) : N.mkQ (s x) = x :=
    congrArg (fun F : (M ⧸ N) →ₗ[ℝ] (M ⧸ N) => F x) hs
  let B : M →ₗ[ℝ] M := s.comp (A.comp N.mkQ)
  have hinside (x : M) : (f - B) x ∈ N := by
    apply (Submodule.Quotient.mk_eq_zero N).mp
    change N.mkQ (f x - s (A (N.mkQ x))) = 0
    rw [map_sub, hsection]
    exact sub_self _
  have hBn (x : N) : B x = 0 := by
    change s (A (N.mkQ x)) = 0
    have hx : N.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero N).mpr x.property
    rw [hx, map_zero, map_zero]
  have hrest : (f - B).restrict (fun x _ => hinside x) = f.restrict hf := by
    ext x
    change f x - B x = f x
    rw [hBn, sub_zero]
  have htraceB : LinearMap.trace ℝ M B = 0 := by
    change LinearMap.trace ℝ M ((s.comp A).comp N.mkQ) = 0
    rw [LinearMap.trace_comp_comm' N.mkQ (s.comp A)]
    have heq : N.mkQ.comp (s.comp A) = A := by
      ext x
      exact hsection (A (N.mkQ x))
    rw [heq]
    exact (LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero
  have ht := LinearMap.trace_restrict_eq_of_forall_mem N (f - B) hinside
  rw [hrest, map_sub, htraceB, sub_zero] at ht
  exact ht.symm

end PolycyclicRecognition

end

end OAI
