import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace OAI

/-! # Preserve independent polynomial coordinates in a domain quotient

This is the domain reduction needed when a commutative algebra of operators
has zero divisors. A prime disjoint from the nonzero polynomial coordinates
preserves their algebraic independence.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped nonZeroDivisors
variable {K C ι : Type} [Field K] [CommRing C] [Algebra K C]

theorem algebraicIndependent_prime_quotient (x : ι → C)
    (hx : AlgebraicIndependent K x) :
    ∃ I : Ideal C, I.IsPrime ∧
      AlgebraicIndependent K (fun i => (Ideal.Quotient.mkₐ K I) (x i)) := by
  classical
  let f : MvPolynomial ι K →ₐ[K] C := MvPolynomial.aeval x
  let S : Submonoid C := (nonZeroDivisors (MvPolynomial ι K)).map f.toMonoidHom
  have hf : Function.Injective f := algebraicIndependent_iff_injective_aeval.mp hx
  have hzero : (0 : C) ∉ S := by
    rintro ⟨p, hp, hp0⟩
    have he : p = 0 := hf (hp0.trans (map_zero f).symm)
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hp) he
  have hd : Disjoint ((⊥ : Ideal C) : Set C) (S : Set C) := by
    apply Set.disjoint_left.mpr
    intro c hc hs
    have he : c = 0 := hc
    exact hzero (he ▸ hs)
  obtain ⟨I, hI, _, hIS⟩ := (⊥ : Ideal C).exists_le_prime_disjoint S hd
  refine ⟨I, hI, ?_⟩
  rw [algebraicIndependent_iff_injective_aeval]
  have he : MvPolynomial.aeval (fun i => (Ideal.Quotient.mkₐ K I) (x i)) =
      (Ideal.Quotient.mkₐ K I).comp f := by
    ext i
    simp [f]
  rw [he]
  apply (injective_iff_map_eq_zero _).mpr
  intro p hp
  by_contra hp0
  have hs : f p ∈ S :=
    ⟨p, mem_nonZeroDivisors_iff_ne_zero.mpr hp0, rfl⟩
  have hi : f p ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hp
  exact Set.disjoint_left.mp hIS hi hs

end PolycyclicRecognition

end

end OAI
