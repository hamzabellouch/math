import OAI.GroupTheory.PolycyclicRecognition.Algebra.CommutingDerivationAction
import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilpotentLatticeLinearAction
import OAI.GroupTheory.PolycyclicRecognition.Lattices.IntegralLatticePowerIndex

namespace OAI

/-! # Extending an integral abelian action on a nilpotent lattice -/

noncomputable section
namespace PolycyclicRecognition.NilpotentLatticeCoordinates
variable {H : Type} [Group H] (C : NilpotentLatticeCoordinates H)

theorem exists_vector_action {n : ℕ} (ρ : IntegralLatticeGroup n →* MulAut H) :
    ∃ m : ℕ, 0 < m ∧ ∃ φ : Multiplicative (Fin n → ℝ) →* MulAut C.carrier,
      ContDiff ℝ ⊤ (fun p : (Fin n → ℝ) × C.carrier => φ (Multiplicative.ofAdd p.1) p.2) ∧
      ∀ z x, (C.equiv (ρ (latticePowerHom n m z) x) : C.carrier) =
        φ (integerVectorHom n z) (C.equiv x) := by
  let A := fun i : Fin n => C.automorphismLieEquiv (ρ (integralLatticeGenerator n i))
  have hA (i j : Fin n) : Commute (A i).toLinearMap (A j).toLinearMap :=
    ((Commute.all (integralLatticeGenerator n i) (integralLatticeGenerator n j)).map ρ).map
      C.automorphismLinear
  obtain ⟨m, hm, D, he, hc⟩ := commuting_lie_automorphisms_have_power_logs A hA
  let φ := PolynomialExponentialCoordinates.commutingDerivationAction D hc
  have hhom : φ.comp (integerVectorHom n) =
      C.automorphismHom.comp (ρ.comp (latticePowerHom n m)) := by
    apply integralLattice_hom_ext
    intro i
    apply DFunLike.ext
    intro x
    change analyticDerivationExp
      (derivationCombination D (integerVectorMap n ((Pi.basisFun ℤ (Fin n)) i))) x =
        C.automorphism (ρ ((integralLatticeGenerator n i) ^ m)) x
    rw [integerVectorMap_basis, derivationCombination_basis, analyticDerivationExp_apply, map_pow]
    rw [← C.automorphismLinear_apply, map_pow]
    exact DFunLike.congr_fun (he i) x
  refine ⟨m, hm, φ, PolynomialExponentialCoordinates.commutingDerivationAction_smooth D hc, ?_⟩
  intro z x
  have h := congrArg (fun f : (IntegralLatticeGroup n →* MulAut C.carrier) =>
    f z (C.equiv x)) hhom
  change φ (integerVectorHom n z) (C.equiv x) =
    C.automorphism (ρ (latticePowerHom n m z)) (C.equiv x) at h
  rw [C.automorphism_on_lattice] at h
  exact h.symm

end PolycyclicRecognition.NilpotentLatticeCoordinates

end

end OAI
