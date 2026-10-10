import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockSector
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockSlaterTensor

namespace OAI

/-! The actual n-particle exterior sector is exactly the Euclidean space
of amplitudes on n-element occupied subsets, with no omitted states. -/

noncomputable section
namespace ContinuumCoulomb.OccupationFock
open Laughlin.Fock SlaterOccupation HubbardGlobal
open scoped BigOperators

variable {Q n : ℕ}

def vector (c : EuclideanSpace ℂ (Occupied Q n)) : Space Q :=
  ∑ S, c S • occupationBasis Q S.val

lemma coordinates_basis (A : Finset (Fin (Q + 1))) :
    fockCoordinates Q (occupationBasis Q A) = EuclideanSpace.single A 1 := by
  classical
  have hb : occupationBasis Q = fockBasis Q := rfl
  rw [hb]
  ext B
  simp only [fockCoordinates_apply, Module.Basis.repr_self, Finsupp.single_apply,
    PiLp.single_apply]
  split_ifs <;> simp_all

lemma vector_coordinates (c : EuclideanSpace ℂ (Occupied Q n)) :
    fockCoordinates Q (vector c) = coordinateInclusion (fun S : Occupied Q n => S.val) c := by
  unfold vector
  rw [map_sum]
  simp_rw [map_smul, coordinates_basis]
  simp only [coordinateInclusion, coordinateInclusionLinear, LinearMap.coe_toContinuousLinearMap',
    LinearMap.coe_mk, AddHom.coe_mk]
  ext A
  simp [Pi.single_apply]

lemma vector_mass (c : EuclideanSpace ℂ (Occupied Q n)) : fockMass (vector c) = ‖c‖ ^ 2 := by
  rw [← fockCoordinates_norm_sq, vector_coordinates,
    coordinateInclusion_norm_map _ Subtype.val_injective]

lemma vector_support (c : EuclideanSpace ℂ (Occupied Q n))
    (A : Finset (Fin (Q + 1))) (hA : A.card ≠ n) : (fockBasis Q).repr (vector c) A = 0 := by
  rw [← fockCoordinates_apply, vector_coordinates]
  apply coordinateInclusion_apply_outside _ c A
  intro S he
  apply hA
  rw [← he]
  exact S.property

lemma exists_vector_of_support (x : Space Q)
    (hx : ∀ A : Finset (Fin (Q + 1)), A.card ≠ n → (fockBasis Q).repr x A = 0) :
    ∃ c : EuclideanSpace ℂ (Occupied Q n), vector c = x := by
  let c : EuclideanSpace ℂ (Occupied Q n) :=
    WithLp.toLp 2 (fun S : Occupied Q n => (fockBasis Q).repr x S.val)
  refine ⟨c, ?_⟩
  apply (fockCoordinates Q).injective
  rw [vector_coordinates]
  ext A
  by_cases hA : A.card = n
  · exact coordinateInclusion_apply_image _ Subtype.val_injective c ⟨A, hA⟩
  · rw [coordinateInclusion_apply_outside _ c A (by
      intro S he
      apply hA
      rw [← he]
      exact S.property)]
    exact (hx A hA).symm

lemma vector_normalizedTensorExterior (c : EuclideanSpace ℂ (Occupied Q n)) :
    vector c = normalizedTensorExterior n Q (FockSlaterTensor.occupationTensor c) :=
  (FockSlaterTensor.normalizedTensorExterior_occupationTensor c).symm

end ContinuumCoulomb.OccupationFock

namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock

theorem isHalfFilled_exists_occupationVector (m : ℕ) (x : Space (2 * m + 1))
    (hx : IsHalfFilled m x) :
    ∃ c : EuclideanSpace ℂ (HalfFilledBasis m), OccupationFock.vector c = x :=
  OccupationFock.exists_vector_of_support x hx

end ContinuumCoulomb.HubbardGlobal

end

end OAI
