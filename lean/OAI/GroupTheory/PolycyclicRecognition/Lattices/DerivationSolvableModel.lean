import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentSemidirectGroup
import OAI.GroupTheory.PolycyclicRecognition.Lattices.SolvableLatticeModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CompactSemidirectModel
import OAI.GroupTheory.PolycyclicRecognition.Lattices.UniformLatticeTransport
import OAI.GroupTheory.PolycyclicRecognition.Lattices.SemidirectUniformLattice
import Mathlib.Analysis.Convex.Contractible

namespace OAI

/-! # The solvable real model of a nilpotent derivation extension -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group.IsSolvable L]
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

def derivationSolvableLieModel : SimplyConnectedSolvableLieModel := by
  let g : Group (L × ℝ) := derivationSemidirectGroup D hD
  let : Mul (L × ℝ) := g.toMul
  let : One (L × ℝ) := g.toOne
  let : Monoid (L × ℝ) := g.toMonoid
  let : MulOneClass (L × ℝ) := g.toMulOneClass
  let : Group (L × ℝ) := g
  let : LieGroup (𝓘(ℝ, L × ℝ)) ⊤ (L × ℝ) := derivationSemidirectLieGroup D hD
  let e : (L × ℝ) ≃* (L ⋊[P.derivationAction D hD] Multiplicative ℝ) :=
    { derivationSemidirectEquiv D hD with map_mul' := fun _ _ => rfl }
  let : Group.IsSolvable (L ⋊[P.derivationAction D hD] Multiplicative ℝ) :=
    semidirect_solvable _
  let : Group.IsSolvable (L × ℝ) :=
    @Group.isSolvable_of_isSolvable_injective (L × ℝ)
      (L ⋊[P.derivationAction D hD] Multiplicative ℝ)
      g inferInstance e.toMonoidHom e.injective inferInstance
  exact { modelSpace := L × ℝ, carrier := L × ℝ }

def derivationModelEquiv : (derivationSolvableLieModel D hD).carrier ≃*
    (L ⋊[P.derivationAction D hD] Multiplicative ℝ) :=
  { derivationSemidirectEquiv D hD with map_mul' := fun _ _ => rfl }

attribute [local instance] semidirectProductTopology

theorem continuous_derivationModelEquiv : Continuous (derivationModelEquiv D hD) := by
  change Continuous ((semidirectProductHomeomorph (P.derivationAction D hD)).symm ∘
    (fun p : L × ℝ => (p.1, Multiplicative.ofAdd p.2)))
  exact (semidirectProductHomeomorph _).symm.continuous.comp continuous_id

theorem continuous_derivationModelEquiv_symm : Continuous (derivationModelEquiv D hD).symm := by
  change Continuous ((fun p : L × Multiplicative ℝ => (p.1, p.2.toAdd)) ∘
    (semidirectProductHomeomorph (P.derivationAction D hD)))
  exact continuous_id.comp (semidirectProductHomeomorph _).continuous

theorem derivationModel_lattice (Λ : Subgroup L) (Δ : Subgroup (Multiplicative ℝ))
    (hstable : ∀ t ∈ Δ, ∀ x ∈ Λ, P.derivationAction D hD t x ∈ Λ)
    (hΛ : IsUniformLattice Λ) (hΔ : IsUniformLattice Δ) :
    IsUniformLattice ((semidirectLattice (P.derivationAction D hD) Λ Δ hstable).comap
      (derivationModelEquiv D hD).toMonoidHom) := by
  exact (semidirectLattice_uniform _ _ _ hstable hΛ hΔ).comap_mulEquiv
    (derivationModelEquiv D hD) (continuous_derivationModelEquiv D hD)
    (continuous_derivationModelEquiv_symm D hD)

end PolycyclicRecognition

end

end OAI
