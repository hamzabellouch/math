import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ControlledCochains
import Mathlib.Data.Finsupp.Defs
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Data.Fintype.Pi

namespace OAI

/-! # Coordinates for scalar homogeneous cochains

The first vertex records translation and the remaining vertices record
relative positions. This identifies controlled-support homogeneous cochains
with arbitrary cochains valued in the group ring.
-/

noncomputable section
namespace PolycyclicRecognition
open Function

variable {G : Type*} [Group G] {n : ℕ}

def homogeneousCoordinates : (Fin (n + 1) → G) ≃ (Fin n → G) × G where
  toFun x := ⟨fun i => (x 0)⁻¹ * x i.succ, (x 0)⁻¹⟩
  invFun p := Fin.cons p.2⁻¹ (fun i => p.2⁻¹ * p.1 i)
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  right_inv p := by
    apply Prod.ext
    · funext i; simp
    · simp

@[simp] theorem homogeneousCoordinates_apply (x : Fin (n + 1) → G) :
    homogeneousCoordinates x = (fun i => (x 0)⁻¹ * x i.succ, (x 0)⁻¹) := rfl

variable {R : Type*} [CommRing R]

/-- Arbitrary group-ring-valued cochains have finite support at each
controlled scale after passing to scalar homogeneous coordinates. -/
theorem controlled_homogeneous_of_finsupp (f : (Fin n → G) → (G →₀ R)) :
    (fun x => f (homogeneousCoordinates x).1 (homogeneousCoordinates x).2) ∈
      controlledCochains R G n := by
  classical
  intro S hS
  let A : Set (Fin n → G) := {a | ∀ i, a i ∈ S}
  have hA : A.Finite := Set.Finite.pi' (fun _ => hS)
  let B : Set ((Fin n → G) × G) := ⋃ a ∈ A, (fun h => (a, h)) '' (f a).support
  have hB : B.Finite := hA.biUnion (fun a _ => (f a).support.finite_toSet.image _)
  apply (hB.preimage homogeneousCoordinates.injective.injOn).subset
  intro x hx
  apply Set.mem_iUnion.mpr
  refine ⟨(homogeneousCoordinates x).1, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
  · intro i
    exact hx.1 0 i.succ
  · refine ⟨(homogeneousCoordinates x).2, ?_, rfl⟩
    exact Finsupp.mem_support_iff.mpr hx.2

/-- Recovering a coefficient function from a homogeneous cochain produces
a finite support, since all translated copies have the same finite scale. -/
theorem finite_support_homogeneous_coefficient (c : controlledCochains R G n)
    (a : Fin n → G) :
    (support (fun h => c (homogeneousCoordinates.symm (a, h)))).Finite := by
  let z : Fin (n + 1) → G := Fin.cons 1 a
  let S : Set G := Set.range (fun p : Fin (n + 1) × Fin (n + 1) => (z p.1)⁻¹ * z p.2)
  have hS : S.Finite := Set.finite_range _
  have hi : Injective (fun h : G => homogeneousCoordinates.symm (a, h)) :=
    homogeneousCoordinates.symm.injective.comp (fun _ _ h => congrArg Prod.snd h)
  apply ((c.property S hS).preimage hi.injOn).subset
  intro h hh
  refine ⟨?_, hh⟩
  intro i j
  refine ⟨(i, j), ?_⟩
  have hc (k : Fin (n + 1)) : homogeneousCoordinates.symm (a, h) k = h⁻¹ * z k := by
    refine Fin.cases ?_ (fun k => ?_) k <;> simp [homogeneousCoordinates, z]
  change (z i)⁻¹ * z j =
    (homogeneousCoordinates.symm (a, h) i)⁻¹ * homogeneousCoordinates.symm (a, h) j
  rw [hc, hc]
  simp [mul_assoc]

/-- The concrete coordinate isomorphism underlying the group-ring
cohomology comparison. No equivariance of the coarse map is needed. -/
def homogeneousCochainEquiv : ((Fin n → G) → (G →₀ R)) ≃ₗ[R] controlledCochains R G n where
  toFun f := ⟨fun x => f (homogeneousCoordinates x).1 (homogeneousCoordinates x).2,
    controlled_homogeneous_of_finsupp f⟩
  invFun c a := Finsupp.ofSupportFinite
    (fun h => c (homogeneousCoordinates.symm (a, h))) (finite_support_homogeneous_coefficient c a)
  left_inv f := by
    funext a
    ext h
    change f (homogeneousCoordinates (homogeneousCoordinates.symm (a, h))).1
      (homogeneousCoordinates (homogeneousCoordinates.symm (a, h))).2 = f a h
    rw [Equiv.apply_symm_apply]
  right_inv c := by
    apply Subtype.ext
    funext x
    change c (homogeneousCoordinates.symm (homogeneousCoordinates x)) = c x
    rw [Equiv.symm_apply_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end PolycyclicRecognition

end

end OAI
