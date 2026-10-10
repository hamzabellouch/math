import OAI.GroupTheory.PolycyclicRecognition.Algebra.AlgebraicConjugationCharacters
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Eigenspace.Basic

namespace OAI

/-! # Detecting eigenvalues by characters on a spanning normal subgroup

A dual eigenvector is nonzero on a spanning family. Restricting it to the
normal subgroup gives the concrete character used by the word-count theorem.
-/

noncomputable section
namespace PolycyclicRecognition
variable {G K V : Type*} [Group G] [Field K] [AddCommGroup V] [Module K V]

theorem exists_conjugation_eigencharacter
    (N : Subgroup G) [N.Normal] (t : G) (q : N →* Multiplicative V)
    (hq : Submodule.span K (Set.range (fun x => (q x).toAdd)) = ⊤)
    (T : V →ₗ[K] V) (hT : ∀ x, (q (MulAut.conjNormal t x)).toAdd = T (q x).toAdd)
    (z : K) (hz : Module.End.HasEigenvalue T.dualMap z) :
    ∃ χ : N →* Multiplicative K, (∃ x, (χ x).toAdd ≠ 0) ∧
      ∀ x, (χ (MulAut.conjNormal t x)).toAdd = z * (χ x).toAdd := by
  obtain ⟨φ, hφ⟩ := hz.exists_hasEigenvector
  have hnz : ∃ x, φ (q x).toAdd ≠ 0 := by
    by_contra! hzero
    apply hφ.2
    apply LinearMap.ext
    intro v
    have hv : v ∈ Submodule.span K (Set.range (fun x => (q x).toAdd)) := by
      rw [hq]
      trivial
    have hle : Submodule.span K (Set.range (fun x => (q x).toAdd)) ≤ φ.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨x, rfl⟩
      exact hzero x
    exact hle hv
  let χ : N →* Multiplicative K := φ.toAddMonoidHom.toMultiplicative.comp q
  refine ⟨χ, hnz, ?_⟩
  intro x
  change φ (q (MulAut.conjNormal t x)).toAdd = z * φ (q x).toAdd
  rw [hT]
  have he := congrArg (fun f : Module.Dual K V => f (q x).toAdd) hφ.apply_eq_smul
  exact he

theorem polynomial_growth_dual_eigenvalue_norm
    [DecidableEq G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hvol : ∃ C d : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d)
    (N : Subgroup G) [N.Normal] (t : G) (q : N →* Multiplicative V)
    (hq : Submodule.span ℂ (Set.range (fun x => (q x).toAdd)) = ⊤)
    (T : V →ₗ[ℂ] V) (hT : ∀ x, (q (MulAut.conjNormal t x)).toAdd = T (q x).toAdd)
    (z : ℂ) (hz : Module.End.HasEigenvalue T.dualMap z) : ‖z‖ = 1 := by
  obtain ⟨χ, ⟨x, hx⟩, hχ⟩ := exists_conjugation_eigencharacter N t q hq T hT z hz
  exact polynomial_growth_conjugation_character_norm_eq_one S hS hgen hvol N t x χ z hχ hx

theorem polynomial_growth_integral_dual_eigenvalue_torsion
    [DecidableEq G] [NumberField K]
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hvol : ∃ C d : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d)
    (N : Subgroup G) [N.Normal] (t : G) (q : N →* Multiplicative V)
    (hq : Submodule.span K (Set.range (fun x => (q x).toAdd)) = ⊤)
    (T : V →ₗ[K] V) (hT : ∀ x, (q (MulAut.conjNormal t x)).toAdd = T (q x).toAdd)
    (z : K) (hz : Module.End.HasEigenvalue T.dualMap z) (hzi : IsIntegral ℤ z) :
    ∃ n : ℕ, 0 < n ∧ z ^ n = 1 := by
  obtain ⟨χ, ⟨x, hx⟩, hχ⟩ := exists_conjugation_eigencharacter N t q hq T hT z hz
  exact polynomial_growth_algebraic_conjugation_character_torsion
    S hS hgen hvol N t x χ z hzi hχ hx

end PolycyclicRecognition

end

end OAI
