import OAI.GroupTheory.PolycyclicRecognition.Geometry.LinearExponentialAction
import OAI.GroupTheory.PolycyclicRecognition.Lattices.SmoothRealActionLattice
import OAI.GroupTheory.PolycyclicRecognition.Lattices.FreeAbelianCyclicLattice

namespace OAI

/-! # The abelian cyclic lattice step from a real matrix logarithm

The real logarithm is a separate, explicit linear algebra obligation. Once
it is provided, the actual Lie model and compact lattice cover are constructed.
-/

noncomputable section
namespace PolycyclicRecognition
variable {d : ℕ}

theorem freeAbelian_cyclic_lattice_of_linear_log
    (a : MulAut (Multiplicative (Fin d → ℤ)))
    (D : AbelianRealSpace d →L[ℝ] AbelianRealSpace d)
    (hD : NormedSpace.exp D =
      (realIntegralLinearEquiv a.toAdditive.toIntLinearEquiv).toContinuousLinearEquiv.toContinuousLinearMap) :
    ∃ (S : SimplyConnectedSolvableLieModel) (Γ : Subgroup S.carrier),
      IsUniformLattice Γ ∧
        Nonempty ((Multiplicative (Fin d → ℤ) ⋊[integerPowerAction a] Multiplicative ℤ) ≃* Γ) := by
  apply smooth_realAction_cyclic_lattice (linearExponentialAction D)
    (linearExponentialAction_smooth D) a (abelianRealLattice d)
    (abelianRealLattice_uniform d) (abelianRealLatticeEquiv d)
  intro x
  rw [linearExponentialAction_apply, one_smul, hD]
  exact (realIntegralGroupAut_lattice a x).symm

end PolycyclicRecognition

end

end OAI
