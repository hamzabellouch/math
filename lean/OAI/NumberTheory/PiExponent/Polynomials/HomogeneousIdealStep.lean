import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Span
import OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientSections

namespace OAI

namespace PiExponentJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k]

theorem homogeneous_mem_step_decomposition
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d n : ℕ} (f p : MvPolynomial σ k)
    (hf : f.IsHomogeneous d) (hp : p.IsHomogeneous (n + d))
    (hmem : p ∈ Ideal.span {f} ⊔ I) :
    ∃ a : MvPolynomial σ k, a.IsHomogeneous n ∧ p - a * f ∈ I := by
  obtain ⟨a, b, hb, hab⟩ := Ideal.mem_span_singleton_sup.mp hmem
  let aₙ := DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ k) a n
  refine ⟨aₙ.1, aₙ.2, ?_⟩
  have hproj := congrArg
    (GradedRing.proj (MvPolynomial.homogeneousSubmodule σ k) (n + d)) hab
  rw [map_add, GradedRing.proj_apply, GradedRing.proj_apply,
    GradedRing.proj_apply,
    DirectSum.coe_decompose_mul_add_of_right_mem
      (MvPolynomial.homogeneousSubmodule σ k) hf,
    DirectSum.decompose_of_mem_same (MvPolynomial.homogeneousSubmodule σ k) hp] at hproj
  have hb' := (Ideal.IsHomogeneous.mem_iff
    (MvPolynomial.homogeneousSubmodule σ k) hI).mp hb (n + d)
  have heq : p - aₙ.1 * f =
      (DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ k) b (n + d) :
        MvPolynomial σ k) := by
    apply sub_eq_iff_eq_add.mpr
    simpa only [aₙ, add_comm] using hproj.symm
  rw [heq]
  exact hb'

theorem homogeneous_mem_step_of_degree_lt
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d n : ℕ} (f p : MvPolynomial σ k)
    (hf : f.IsHomogeneous d) (hp : p.IsHomogeneous n) (hnd : n < d)
    (hmem : p ∈ Ideal.span {f} ⊔ I) : p ∈ I := by
  obtain ⟨a, b, hb, hab⟩ := Ideal.mem_span_singleton_sup.mp hmem
  have hproj := congrArg
    (GradedRing.proj (MvPolynomial.homogeneousSubmodule σ k) n) hab
  rw [map_add, GradedRing.proj_apply, GradedRing.proj_apply,
    GradedRing.proj_apply,
    DirectSum.coe_decompose_mul_of_right_mem_of_not_le
      (MvPolynomial.homogeneousSubmodule σ k) hf (Nat.not_le_of_lt hnd),
    zero_add,
    DirectSum.decompose_of_mem_same (MvPolynomial.homogeneousSubmodule σ k) hp] at hproj
  rw [← hproj]
  exact (Ideal.IsHomogeneous.mem_iff
    (MvPolynomial.homogeneousSubmodule σ k) hI).mp hb n

end PiExponentJets.W64

end OAI
