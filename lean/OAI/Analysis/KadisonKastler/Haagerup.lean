import OAI.Analysis.KadisonKastler.CompletelyBounded
import OAI.Analysis.KadisonKastler.StarCorrection
import Mathlib.Algebra.Algebra.Bilinear

namespace OAI

/-!
# Row-column bounds for bilinear multiplication

The Haagerup bound is expressed directly by all finite rectangular matrix
products, as in the UCP criterion of §2 of *Universal strong
Kadison–Kastler stability* (2026). For multiplication transported through
a linear equivalence, this is exactly the matrix defect already bounded
in `CompletelyBounded`.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder A] [StarOrderedRing A] in
/-- The row-column extension of a bilinear product to rectangular matrices. -/
def bilinearProduct (m : A →ₗ[ℂ] A →ₗ[ℂ] A) {p r q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin q) A) :
    CStarMatrix (Fin p) (Fin q) A :=
  CStarMatrix.ofMatrix fun i k => ∑ j, m (X i j) (Y j k)

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem bilinearProduct_apply (m : A →ₗ[ℂ] A →ₗ[ℂ] A) {p r q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin q) A)
    (i : Fin p) (k : Fin q) :
    bilinearProduct m X Y i k = ∑ j, m (X i j) (Y j k) := rfl

/-- The norm bound on the bilinear map viewed on the Haagerup product,
in its concrete finite row-column formulation. -/
def HaagerupBound (m : A →ₗ[ℂ] A →ₗ[ℂ] A) (c : ℝ) : Prop :=
  ∀ (p r q : ℕ) (X : CStarMatrix (Fin p) (Fin r) A)
    (Y : CStarMatrix (Fin r) (Fin q) A),
    ‖bilinearProduct m X Y‖ ≤ c * ‖X‖ * ‖Y‖

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
/-- Transported multiplication as a bundled complex-bilinear product. -/
def transportedBilinear (F : A ≃ₗ[ℂ] B) : A →ₗ[ℂ] A →ₗ[ℂ] A where
  toFun x :=
    { toFun := transportedMul F x
      map_add' y z := transportedMul_add_right F x y z
      map_smul' c y := transportedMul_smul_right F c x y }
  map_add' x y := by
    ext z
    exact transportedMul_add_left F x y z
  map_smul' c x := by
    ext y
    exact transportedMul_smul_left F c x y

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem transportedBilinear_apply (F : A ≃ₗ[ℂ] B) (x y : A) :
    transportedBilinear F x y = transportedMul F x y := rfl

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
/-- Associativity of the bundled transported product. -/
theorem transportedBilinear_assoc (F : A ≃ₗ[ℂ] B) (x y z : A) :
    transportedBilinear F (transportedBilinear F x y) z =
      transportedBilinear F x (transportedBilinear F y z) :=
  transportedMul_assoc F x y z

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
/-- Star compatibility of the bundled transported product. -/
theorem transportedBilinear_star (F : A ≃ₗ[ℂ] B)
    (hstar : ∀ x, F (star x) = star (F x)) (x y : A) :
    star (transportedBilinear F x y) = transportedBilinear F (star y) (star x) :=
  transportedMul_star F hstar x y

omit [PartialOrder A] [StarOrderedRing A] in
/-- The ordinary bilinear multiplication extends to the usual rectangular
matrix product. -/
@[simp] theorem bilinearProduct_mul {p r q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin q) A) :
    bilinearProduct (LinearMap.mul ℂ A) X Y = X * Y := by
  ext i k
  rfl

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
/-- Exact equality between the row-column bilinear defect and the matrix
defect of multiplication transported through `F`. -/
theorem bilinearProduct_transported_defect (F : A ≃ₗ[ℂ] B) {p r q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin q) A) :
    bilinearProduct (transportedBilinear F - LinearMap.mul ℂ A) X Y =
      CStarMatrix.mapₗ F.symm.toLinearMap
        (CStarMatrix.mapₗ F.toLinearMap X * CStarMatrix.mapₗ F.toLinearMap Y) - X * Y := by
  ext i k
  change (∑ j, (F.symm (F (X i j) * F (Y j k)) - X i j * Y j k)) =
    F.symm (∑ j, F (X i j) * F (Y j k)) - ∑ j, X i j * Y j k
  rw [map_sum, Finset.sum_sub_distrib]

omit [PartialOrder B] [StarOrderedRing B] in
/-- The transported-product matrix estimate is precisely the Haagerup bound
on the difference between transported and original multiplication. -/
theorem haagerupBound_transported_defect_iff (F : A ≃ₗ[ℂ] B) (c : ℝ) :
    HaagerupBound (transportedBilinear F - LinearMap.mul ℂ A) c ↔
      TransportedProductBound F c := by
  constructor
  · intro h p r q X Y
    simpa only [bilinearProduct_transported_defect] using h p r q X Y
  · intro h p r q X Y
    simpa only [bilinearProduct_transported_defect] using h p r q X Y

end

end KadisonKastler

end OAI
