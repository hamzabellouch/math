import OAI.GroupTheory.PolycyclicRecognition.Lattices.LatticeWordExtension
import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilpotentCyclicLatticeExtension

namespace OAI

/-! # The cyclic lattice step with its automorphism extension constructed

Only the kernel's ordered polynomial coordinates are supplied. Conjugation
extends by real generator powers; its finite logarithm supplies the real
action in the new Lie model.
-/

noncomputable section
namespace PolycyclicRecognition
open Module
variable {H L : Type} [Group H] [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group.IsSolvable L]

theorem ordered_cyclic_lattice_extension (a : MulAut H)
    [Group.IsNilpotent (H ⋊[integerPowerAction a] Multiplicative ℤ)]
    {d : ℕ} (b : Basis (Fin d) ℝ L) (p : L ≃ L)
    (hp : IsPolynomialInBasis b b p) (hq : IsPolynomialInBasis b b p.symm)
    (Λ : Subgroup L) (hΛ : IsUniformLattice Λ) (e : H ≃* Λ)
    (X : Fin d → H) (hX : Function.Surjective (orderedWord X))
    (hparam : ∀ z : Fin d → ℤ,
      p (b.equivFun.symm (fun i => (z i : ℝ))) = (e (orderedWord X z) : L)) :
    ∃ (S : SimplyConnectedSolvableLieModel) (Γ : Subgroup S.carrier),
      IsUniformLattice Γ ∧
        Nonempty ((H ⋊[integerPowerAction a] Multiplicative ℤ) ≃* Γ) := by
  let j := Λ.subtype.comp e.toMonoidHom
  exact nilpotent_cyclic_lattice_extension a b p hp p.surjective Λ hΛ e
    (fun z => ⟨orderedWord X z, (hparam z).symm⟩)
    (latticeWordAut b p j X hp hq hparam hX a)
    (contMDiff_latticeWordAut b p j X hp hq hparam hX a)
    (latticeWordAut_on_lattice b p j X hp hq hparam hX a)

end PolycyclicRecognition

end

end OAI
