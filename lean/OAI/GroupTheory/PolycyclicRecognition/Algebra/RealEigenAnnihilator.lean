import OAI.GroupTheory.PolycyclicRecognition.Algebra.DerivationEigenvectors
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Algebra.Polynomial.Splits

namespace OAI

/-! # A real split annihilator from spanning real eigenvectors -/

noncomputable section
namespace PolycyclicRecognition

open Polynomial Module

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  (D : Module.End ℝ V)

def realEigenPolynomial : ℝ[X] := ∏ r : D.Eigenvalues, (X - C (r : ℝ))

theorem realEigenPolynomial_monic : (realEigenPolynomial D).Monic := by
  classical
  exact monic_prod_of_monic _ _ fun r _ => monic_X_sub_C (r : ℝ)

theorem realEigenPolynomial_splits : (realEigenPolynomial D).Splits := by
  classical
  exact Splits.prod fun r _ => Splits.X_sub_C (r : ℝ)

theorem realEigenPolynomial_annihilates (hspan : (⨆ r : ℝ, D.eigenspace r) = ⊤) :
    aeval D (realEigenPolynomial D) = 0 := by
  classical
  let : Fintype {r // D.HasUnifEigenvalue r 1} := inferInstanceAs (Fintype D.Eigenvalues)
  ext v
  have hv : v ∈ ⨆ r : ℝ, D.eigenspace r := by
    rw [hspan]
    trivial
  apply Submodule.iSup_induction (fun r : ℝ => D.eigenspace r)
    (motive := fun v => aeval D (realEigenPolynomial D) v = 0) hv
  · intro r v hvr
    by_cases hv0 : v = 0
    · simp [hv0]
    · have hr : D.HasEigenvalue r := D.hasEigenvalue_of_hasEigenvector ⟨hvr, hv0⟩
      have hz : (realEigenPolynomial D).eval r = 0 := by
        change (Polynomial.evalRingHom r) (∏ t : D.Eigenvalues, (X - C (t : ℝ))) = 0
        rw [map_prod]
        apply Finset.prod_eq_zero (Finset.mem_univ (⟨r, hr⟩ : D.Eigenvalues))
        simp
      rw [D.aeval_apply_of_mem_apply_eq_smul (Module.End.mem_eigenspace_iff.mp hvr), hz, zero_smul]
  · simp
  · intro u v hu hv
    simp only [map_add, hu, hv, add_zero]

end PolycyclicRecognition

end

end OAI
