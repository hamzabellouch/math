import Mathlib.Order.Minimal
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

namespace OAI

namespace PiExponentJets.W22

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Finite σ]

omit [Finite σ] in
theorem homogeneous_colon_singleton
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} {f : MvPolynomial σ k} (hf : f.IsHomogeneous d) :
    (I.colon {f}).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := by
  intro n a ha
  apply Submodule.mem_colon_singleton.mpr
  have haf : a * f ∈ I := by simpa only [smul_eq_mul] using
    (Submodule.mem_colon_singleton.mp ha)
  have h := hI (n + d) haf
  rw [DirectSum.coe_decompose_mul_add_of_right_mem
    (MvPolynomial.homogeneousSubmodule σ k) hf] at h
  exact h

theorem exists_homogeneous_prime_colon
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hproper : I ≠ ⊤) :
    ∃ (d : ℕ) (f : MvPolynomial σ k), f.IsHomogeneous d ∧ f ∉ I ∧
      (I.colon {f}).IsPrime := by
  classical
  let candidates : Ideal (MvPolynomial σ k) → Prop := fun P =>
    ∃ d f, f.IsHomogeneous d ∧ f ∉ I ∧ P = I.colon {f}
  have hnonempty : ∃ P, candidates P := by
    refine ⟨I.colon {(1 : MvPolynomial σ k)}, 0, 1, ?_, ?_, rfl⟩
    · exact MvPolynomial.isHomogeneous_one σ k
    · exact fun h => hproper (Ideal.eq_top_of_isUnit_mem I h isUnit_one)
  obtain ⟨P, hP, hmax⟩ := exists_maximal_of_wellFoundedGT candidates hnonempty
  obtain ⟨d, f, hf, hfI, rfl⟩ := hP
  refine ⟨d, f, hf, hfI, ?_⟩
  apply (homogeneous_colon_singleton I hI hf).isPrime_of_homogeneous_mem_or_mem
  · intro htop
    have h : (1 : MvPolynomial σ k) ∈ I.colon {f} := by
      rw [htop]
      trivial
    exact hfI (by simpa only [Submodule.mem_colon_singleton, one_smul] using h)
  · intro a b ha hb hab
    by_cases hbI : b ∈ I.colon {f}
    · exact Or.inr hbI
    · left
      obtain ⟨e, he⟩ := hb
      have hb' : b.IsHomogeneous e := he
      have hbf : (b * f).IsHomogeneous (e + d) := hb'.mul hf
      have hbfI : b * f ∉ I := by
        simpa only [Submodule.mem_colon_singleton, smul_eq_mul] using hbI
      have hle : I.colon {f} ≤ I.colon {b * f} := by
        intro r hr
        apply Submodule.mem_colon_singleton.mpr
        have hrf : r * f ∈ I := by
          simpa only [smul_eq_mul] using (Submodule.mem_colon_singleton.mp hr)
        simpa only [smul_eq_mul, mul_left_comm r b f] using I.mul_mem_left b hrf
      have hback : I.colon {b * f} ≤ I.colon {f} :=
        hmax ⟨e + d, b * f, hbf, hbfI, rfl⟩ hle
      apply hback
      apply Submodule.mem_colon_singleton.mpr
      simpa only [smul_eq_mul, mul_assoc] using (Submodule.mem_colon_singleton.mp hab)

end PiExponentJets.W22

end OAI
