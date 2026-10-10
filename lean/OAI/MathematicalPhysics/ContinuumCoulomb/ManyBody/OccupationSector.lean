import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.OccupationFock

namespace OAI

/-! The occupation-amplitude map is a linear equivalence onto the entire
fixed-particle exterior sector, preserving its actual occupation inner
product. No state in that sector is excluded. -/

noncomputable section
namespace ContinuumCoulomb.OccupationFock
open Laughlin.Fock SlaterOccupation HubbardGlobal
open scoped BigOperators InnerProductSpace

variable {Q n : ℕ}

def coordinateIsometry (Q n : ℕ) :
    EuclideanSpace ℂ (Occupied Q n) →ₗᵢ[ℂ] FockCoordinateSpace Q where
  toLinearMap := (coordinateInclusion (fun S : Occupied Q n => S.val)).toLinearMap
  norm_map' := coordinateInclusion_norm_map _ Subtype.val_injective

lemma vector_injective : Function.Injective (vector (Q := Q) (n := n)) := by
  intro c d h
  have hc := congrArg (fockCoordinates Q) h
  rw [vector_coordinates, vector_coordinates] at hc
  exact (coordinateIsometry Q n).injective hc

lemma vector_inner (c d : EuclideanSpace ℂ (Occupied Q n)) :
    occupationInner Q (vector c) (vector d) = ⟪c, d⟫_ℂ := by
  have h := (coordinateIsometry Q n).inner_map_map c d
  change ⟪coordinateInclusion (fun S : Occupied Q n => S.val) c,
    coordinateInclusion (fun S : Occupied Q n => S.val) d⟫_ℂ = _ at h
  rw [← vector_coordinates, ← vector_coordinates] at h
  simpa only [PiLp.inner_apply, RCLike.inner_apply', fockCoordinates_apply,
    occupationInner, occupationBasis, fockBasis, starRingEnd_apply] using h

def particleSector (Q n : ℕ) : Submodule ℂ (Space Q) where
  carrier := {x | ∀ A : Finset (Fin (Q + 1)), A.card ≠ n → (fockBasis Q).repr x A = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy A hA
    simp only [map_add, Finsupp.add_apply, hx A hA, hy A hA, add_zero]
  smul_mem' := by
    intro c x hx A hA
    simp only [map_smul, Finsupp.smul_apply, hx A hA, smul_zero]

def synthesisLinear (Q n : ℕ) : EuclideanSpace ℂ (Occupied Q n) →ₗ[ℂ] Space Q where
  toFun := vector
  map_add' c d := by simp [vector, add_smul, Finset.sum_add_distrib]
  map_smul' c d := by simp [vector, smul_smul, Finset.smul_sum]

def sectorSynthesis (Q n : ℕ) :
    EuclideanSpace ℂ (Occupied Q n) →ₗ[ℂ] particleSector Q n :=
  (synthesisLinear Q n).codRestrict (particleSector Q n) (fun c => vector_support c)

def sectorEquiv (Q n : ℕ) :
    EuclideanSpace ℂ (Occupied Q n) ≃ₗ[ℂ] particleSector Q n :=
  LinearEquiv.ofBijective (sectorSynthesis Q n) (by
    constructor
    · intro c d h
      exact vector_injective (congrArg Subtype.val h)
    · intro x
      obtain ⟨c, hc⟩ := exists_vector_of_support x.val x.property
      exact ⟨c, Subtype.ext hc⟩)

@[simp] lemma sectorEquiv_apply (c : EuclideanSpace ℂ (Occupied Q n)) :
    (sectorEquiv Q n c).val = vector c := rfl

lemma sectorEquiv_inner (c d : EuclideanSpace ℂ (Occupied Q n)) :
    occupationInner Q (sectorEquiv Q n c).val (sectorEquiv Q n d).val = ⟪c, d⟫_ℂ :=
  vector_inner c d

lemma sectorEquiv_mass (c : EuclideanSpace ℂ (Occupied Q n)) :
    fockMass (sectorEquiv Q n c).val = ‖c‖ ^ 2 := vector_mass c

end ContinuumCoulomb.OccupationFock

end

end OAI
