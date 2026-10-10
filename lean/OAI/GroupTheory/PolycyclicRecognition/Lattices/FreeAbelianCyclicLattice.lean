import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianRealSpace
import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilpotentCyclicLatticeExtension
import Mathlib.Algebra.Group.Equiv.TypeTags

namespace OAI

/-! # Realizing nilpotent integral abelian-by-cyclic groups as Lie lattices

The nilpotency class is unrestricted. The real action is constructed by the
finite logarithm of the extended integral automorphism.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {d : ℕ}

def realIntegralGroupAut (a : MulAut (Multiplicative (Fin d → ℤ))) :
    MulAut (AbelianRealSpace d) :=
  { (realIntegralLinearEquiv a.toAdditive.toIntLinearEquiv).toEquiv with
    map_mul' := fun x y => (realIntegralLinearEquiv a.toAdditive.toIntLinearEquiv).map_add x y }

theorem contMDiff_realIntegralGroupAut (a : MulAut (Multiplicative (Fin d → ℤ))) :
    ContMDiff (𝓘(ℝ, AbelianRealSpace d)) (𝓘(ℝ, AbelianRealSpace d)) ∞ (realIntegralGroupAut a) :=
  (realIntegralLinearEquiv a.toAdditive.toIntLinearEquiv).toContinuousLinearEquiv.contDiff.contMDiff

theorem realIntegralGroupAut_lattice (a : MulAut (Multiplicative (Fin d → ℤ)))
    (x : Multiplicative (Fin d → ℤ)) :
    realIntegralGroupAut a (abelianRealLatticeEquiv d x) =
      (abelianRealLatticeEquiv d (a x) : AbelianRealSpace d) := by
  rw [abelianRealLatticeEquiv_apply, abelianRealLatticeEquiv_apply]
  exact realIntegralLinearEquiv_cast a.toAdditive.toIntLinearEquiv x.toAdd

theorem freeAbelian_cyclic_nilpotent_lattice
    (a : MulAut (Multiplicative (Fin d → ℤ)))
    [Group.IsNilpotent (Multiplicative (Fin d → ℤ) ⋊[integerPowerAction a] Multiplicative ℤ)] :
    ∃ (S : SimplyConnectedSolvableLieModel) (Γ : Subgroup S.carrier),
      IsUniformLattice Γ ∧
        Nonempty ((Multiplicative (Fin d → ℤ) ⋊[integerPowerAction a] Multiplicative ℤ) ≃* Γ) := by
  let b : Module.Basis (Fin d) ℝ (AbelianRealSpace d) := Pi.basisFun ℝ (Fin d)
  refine nilpotent_cyclic_lattice_extension a b id
    (IsPolynomialInBasis.linear (LinearMap.id : AbelianRealSpace d →ₗ[ℝ] AbelianRealSpace d))
    Function.surjective_id (abelianRealLattice d) (abelianRealLattice_uniform d)
    (abelianRealLatticeEquiv d) ?_ (realIntegralGroupAut a)
    (contMDiff_realIntegralGroupAut a) (realIntegralGroupAut_lattice a)
  intro z
  refine ⟨Multiplicative.ofAdd z, ?_⟩
  rw [abelianRealLatticeEquiv_apply]
  change (fun i => (z i : ℝ)) = (Pi.basisFun ℝ (Fin d)).equivFun.symm (fun i => (z i : ℝ))
  rw [Pi.basisFun_equivFun]
  rfl

end PolycyclicRecognition

end

end OAI
