import OAI.GroupTheory.PolycyclicRecognition.Algebra.CommutingDerivationAction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialModelHom
import OAI.GroupTheory.PolycyclicRecognition.Lattices.IntegralLatticePowerIndex

namespace OAI

/-! # Extending a smooth integral action on a nilpotent group

The integral action need not preserve a particular kernel lattice. Passing to
a common finite-index power gives a genuine multiparameter Lie action.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [PolynomialExponentialCoordinates L]

theorem smooth_integral_action_has_vector_extension {n : ℕ}
    (ρ : IntegralLatticeGroup n →* MulAut L)
    (hρ : ∀ z, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (ρ z)) :
    ∃ m : ℕ, 0 < m ∧ ∃ φ : Multiplicative (Fin n → ℝ) →* MulAut L,
      ContDiff ℝ ⊤ (fun p : (Fin n → ℝ) × L => φ (Multiplicative.ofAdd p.1) p.2) ∧
      ∀ z x, ρ (latticePowerHom n m z) x = φ (integerVectorHom n z) x := by
  let A := fun i : Fin n => polynomialModelLieEquiv
    (ρ (integralLatticeGenerator n i)) (hρ (integralLatticeGenerator n i))
  have hA (i j : Fin n) : Commute (A i).toLinearMap (A j).toLinearMap := by
    apply LinearMap.ext
    intro x
    change A i (A j x) = A j (A i x)
    simp only [A, polynomialModelLieEquiv_apply]
    exact DFunLike.congr_fun
      (((Commute.all (integralLatticeGenerator n i) (integralLatticeGenerator n j)).map ρ).eq) x
  obtain ⟨m, hm, D, he, hc⟩ := commuting_lie_automorphisms_have_power_logs A hA
  let φ := PolynomialExponentialCoordinates.commutingDerivationAction D hc
  have hp (i : Fin n) (k : ℕ) (x : L) :
      ((A i).toLinearMap ^ k) x = ρ ((integralLatticeGenerator n i) ^ k) x := by
    induction k generalizing x with
    | zero => simp only [pow_zero, map_one, Module.End.one_apply, MulAut.one_apply]
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ', map_mul]
      exact polynomialModelLieEquiv_apply _ _ _
  have hhom : φ.comp (integerVectorHom n) = ρ.comp (latticePowerHom n m) := by
    apply integralLattice_hom_ext
    intro i
    apply DFunLike.ext
    intro x
    change analyticDerivationExp
      (derivationCombination D (integerVectorMap n ((Pi.basisFun ℤ (Fin n)) i))) x =
        ρ ((integralLatticeGenerator n i) ^ m) x
    rw [integerVectorMap_basis, derivationCombination_basis, analyticDerivationExp_apply]
    exact (DFunLike.congr_fun (he i) x).trans (hp i m x)
  refine ⟨m, hm, φ, PolynomialExponentialCoordinates.commutingDerivationAction_smooth D hc, ?_⟩
  intro z x
  exact (congrArg (fun F : IntegralLatticeGroup n →* MulAut L => F z x) hhom).symm

end PolycyclicRecognition

end

end OAI
