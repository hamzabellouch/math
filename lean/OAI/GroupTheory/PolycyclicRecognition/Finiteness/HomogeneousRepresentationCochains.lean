import OAI.GroupTheory.PolycyclicRecognition.Algebra.ControlledGroupRingCoefficients
import Mathlib.RepresentationTheory.Homological.Resolution
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

namespace OAI

/-! # Controlled cochains as maps from the standard resolution

The coefficient at the identity of an equivariant group-ring-valued map
recovers the scalar cochain. Conversely diagonal translation reconstructs
that equivariant map, with finite support supplied by controlled-support estimates.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {G R : Type} [Group G] [CommRing R] {n : ℕ}

def homogeneousGroupRingValue (c : controlledCochains R G n) (x : Fin (n + 1) → G) :
    MonoidAlgebra R G := (MonoidAlgebra.coeffLinearEquiv R).symm (controlledGroupRingValue c x)

@[simp] theorem homogeneousGroupRingValue_coeff (c : controlledCochains R G n)
    (x : Fin (n + 1) → G) (h : G) :
    (homogeneousGroupRingValue c x).coeff h = c (fun i => h⁻¹ * x i) := rfl

theorem homogeneousGroupRingValue_covariance (c : controlledCochains R G n)
    (x : Fin (n + 1) → G) (g : G) :
    homogeneousGroupRingValue c (g • x) =
      Representation.leftRegular R G g (homogeneousGroupRingValue c x) := by
  ext h
  simp only [homogeneousGroupRingValue_coeff, Representation.coeff_ofMulAction]
  exact controlledGroupRingValue_covariance c x g h

def homogeneousGroupRingLinear (c : controlledCochains R G n) :
    MonoidAlgebra R (Fin (n + 1) → G) →ₗ[R] MonoidAlgebra R G :=
  (Finsupp.linearCombination R (homogeneousGroupRingValue c)).comp
    (MonoidAlgebra.coeffLinearEquiv R).toLinearMap

@[simp] theorem homogeneousGroupRingLinear_single (c : controlledCochains R G n)
    (x : Fin (n + 1) → G) (r : R) :
    homogeneousGroupRingLinear c (MonoidAlgebra.single x r) = r • homogeneousGroupRingValue c x := by
  simp [homogeneousGroupRingLinear]

/-- The reconstructed values give an actual morphism of group representations. -/
def homogeneousRepresentationCochain (c : controlledCochains R G n) :
    (Rep.standardComplex R G).X n ⟶ Rep.leftRegular R G :=
  Rep.ofHom
    { toLinearMap := homogeneousGroupRingLinear c
      isIntertwining' := fun g => by
        change (homogeneousGroupRingLinear c).comp (Representation.diagonal R G (n + 1) g) =
          (Representation.leftRegular R G g).comp (homogeneousGroupRingLinear c)
        refine MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_
        change homogeneousGroupRingLinear c
            (Representation.diagonal R G (n + 1) g (MonoidAlgebra.single x 1)) =
          Representation.leftRegular R G g
            (homogeneousGroupRingLinear c (MonoidAlgebra.single x 1))
        simp only [Representation.ofMulAction_single,
          homogeneousGroupRingLinear_single, one_smul]
        exact homogeneousGroupRingValue_covariance c x g }

@[simp] theorem homogeneousRepresentationCochain_single_coeff
    (c : controlledCochains R G n) (x : Fin (n + 1) → G) :
    ((homogeneousRepresentationCochain c).hom (MonoidAlgebra.single x 1)).coeff 1 = c x := by
  change (homogeneousGroupRingLinear c (MonoidAlgebra.single x 1)).coeff 1 = c x
  simp

theorem representationCochain_translate
    (F : (Rep.standardComplex R G).X n ⟶ Rep.leftRegular R G)
    (x : Fin (n + 1) → G) (g : G) :
    (F.hom (MonoidAlgebra.single (g • x) 1)).coeff 1 =
      (F.hom (MonoidAlgebra.single x 1)).coeff g⁻¹ := by
  have h := Rep.hom_comm_apply F g (MonoidAlgebra.single x 1)
  change F.hom (Representation.diagonal R G (n + 1) g (MonoidAlgebra.single x 1)) =
    Representation.leftRegular R G g (F.hom (MonoidAlgebra.single x 1)) at h
  rw [Representation.ofMulAction_single] at h
  have hc := congrArg (fun v : MonoidAlgebra R G => v.coeff 1) h
  change (F.hom (MonoidAlgebra.single (g • x) 1)).coeff 1 =
    (Representation.leftRegular R G g (F.hom (MonoidAlgebra.single x 1))).coeff 1 at hc
  simpa only [Representation.coeff_ofMulAction, smul_eq_mul, mul_one] using hc

/-- Evaluation at the identity has controlled support for every equivariant
map from the homogeneous resolution. -/
theorem representationCochain_controlled
    (F : (Rep.standardComplex R G).X n ⟶ Rep.leftRegular R G) :
    (fun x => (F.hom (MonoidAlgebra.single x 1)).coeff 1) ∈
      controlledCochains R G n := by
  let f : (Fin n → G) → (G →₀ R) := fun a =>
    MonoidAlgebra.coeffLinearEquiv R (F.hom (MonoidAlgebra.single (Fin.cons 1 a) 1))
  have heq : (fun x => f (homogeneousCoordinates x).1 (homogeneousCoordinates x).2) =
      (fun x => (F.hom (MonoidAlgebra.single x 1)).coeff 1) := by
    funext x
    let z : Fin (n + 1) → G := Fin.cons 1 (fun i => (x 0)⁻¹ * x i.succ)
    have hz : x 0 • z = x := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [z]
    have h := representationCochain_translate F z (x 0)
    rw [hz] at h
    exact h.symm
  rw [← heq]
  exact controlled_homogeneous_of_finsupp f

/-- Scalar coefficient extraction, with its support obligation proved. -/
def representationControlledCochain
    (F : (Rep.standardComplex R G).X n ⟶ Rep.leftRegular R G) :
    controlledCochains R G n :=
  ⟨fun x => (F.hom (MonoidAlgebra.single x 1)).coeff 1,
    representationCochain_controlled F⟩

@[simp] theorem representationControlledCochain_homogeneous
    (c : controlledCochains R G n) :
    representationControlledCochain (homogeneousRepresentationCochain c) = c := by
  apply Subtype.ext
  funext x
  exact homogeneousRepresentationCochain_single_coeff c x

@[simp] theorem homogeneousRepresentationCochain_controlled
    (F : (Rep.standardComplex R G).X n ⟶ Rep.leftRegular R G) :
    homogeneousRepresentationCochain (representationControlledCochain F) = F := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  refine MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_
  change Fin (n + 1) → G at x
  change homogeneousGroupRingLinear (representationControlledCochain F)
      (MonoidAlgebra.single x 1) = F.hom (MonoidAlgebra.single x 1)
  rw [homogeneousGroupRingLinear_single, one_smul]
  ext h
  change (F.hom (MonoidAlgebra.single (fun i => h⁻¹ * x i) 1)).coeff 1 =
    (F.hom (MonoidAlgebra.single x 1)).coeff h
  have hx := representationCochain_translate (n := n) F (x : Fin (n + 1) → G) h⁻¹
  change (F.hom (MonoidAlgebra.single (fun i => h⁻¹ * x i) 1)).coeff 1 =
    (F.hom (MonoidAlgebra.single x 1)).coeff (h⁻¹)⁻¹ at hx
  simpa only [inv_inv] using hx

/-- Controlled scalar cochains are exactly the equivariant cochains with
coefficients in the left regular group ring. -/
def homogeneousRepresentationCochainEquiv :
    controlledCochains R G n ≃ₗ[R]
      ((Rep.standardComplex R G).X n ⟶ Rep.leftRegular R G) where
  toFun := homogeneousRepresentationCochain
  invFun := representationControlledCochain
  left_inv := representationControlledCochain_homogeneous
  right_inv := homogeneousRepresentationCochain_controlled
  map_add' c d := by
    apply (Function.LeftInverse.injective homogeneousRepresentationCochain_controlled)
    apply Subtype.ext
    funext x
    change ((homogeneousRepresentationCochain (c + d)).hom
      (MonoidAlgebra.single x 1)).coeff 1 =
      ((homogeneousRepresentationCochain c).hom (MonoidAlgebra.single x 1) +
        (homogeneousRepresentationCochain d).hom (MonoidAlgebra.single x 1)).coeff 1
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact (homogeneousRepresentationCochain_single_coeff (c + d) x).trans
      (congrArg₂ (· + ·) (homogeneousRepresentationCochain_single_coeff c x)
        (homogeneousRepresentationCochain_single_coeff d x)).symm
  map_smul' r c := by
    apply (Function.LeftInverse.injective homogeneousRepresentationCochain_controlled)
    apply Subtype.ext
    funext x
    change ((homogeneousRepresentationCochain (r • c)).hom
      (MonoidAlgebra.single x 1)).coeff 1 =
      (r • (homogeneousRepresentationCochain c).hom (MonoidAlgebra.single x 1)).coeff 1
    simp only [MonoidAlgebra.coeff_smul, Finsupp.smul_apply]
    exact (homogeneousRepresentationCochain_single_coeff (r • c) x).trans
      (congrArg (r • ·) (homogeneousRepresentationCochain_single_coeff c x)).symm

end PolycyclicRecognition

end

end OAI
