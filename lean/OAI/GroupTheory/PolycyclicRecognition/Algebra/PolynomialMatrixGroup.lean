import OAI.GroupTheory.PolycyclicRecognition.Analysis.AffinePolynomialTopology
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Topology.Algebra.Monoid

namespace OAI

/-! # Polynomial topology on invertible matrices

Both a matrix and its inverse are retained as affine coordinates. Inversion
then exchanges coordinates, and translations are polynomial coordinate maps.
The resulting topology is Noetherian and T1. Only separate continuity of
multiplication is asserted; the product topology need not be the affine
polynomial topology on a product.
-/

noncomputable section
namespace PolycyclicRecognition

@[ext]
structure PolynomialMatrixGroup (K : Type*) (n : ℕ) [Field K] where
  toGL : Matrix.GeneralLinearGroup (Fin n) K

namespace PolynomialMatrixGroup

variable {K : Type*} [Field K] {n : ℕ}

def equivGL : PolynomialMatrixGroup K n ≃ Matrix.GeneralLinearGroup (Fin n) K where
  toFun := toGL
  invFun := PolynomialMatrixGroup.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : Group (PolynomialMatrixGroup K n) := equivGL.group

def mulEquivGL : PolynomialMatrixGroup K n ≃* Matrix.GeneralLinearGroup (Fin n) K :=
  { equivGL with map_mul' := fun _ _ => rfl }

def entries (g : PolynomialMatrixGroup K n) : Matrix (Fin n) (Fin n) K := g.toGL.val

@[simp] theorem entries_mul (g h : PolynomialMatrixGroup K n) :
    entries (g * h) = entries g * entries h := rfl

abbrev Coord (n : ℕ) := Bool × Fin n × Fin n

def coordinates (g : PolynomialMatrixGroup K n) : AffinePolynomialPoint (Coord n) K :=
  ⟨fun s => if s.1 then entries g⁻¹ s.2.1 s.2.2 else entries g s.2.1 s.2.2⟩

theorem coordinates_injective : Function.Injective (coordinates (K := K) (n := n)) := by
  intro g h he
  apply PolynomialMatrixGroup.ext
  apply Units.ext
  ext i j
  exact congrArg (fun x : AffinePolynomialPoint (Coord n) K => x.coord (false, i, j)) he

instance : TopologicalSpace (PolynomialMatrixGroup K n) :=
  TopologicalSpace.induced coordinates inferInstance

theorem inducing_coordinates : Topology.IsInducing (coordinates (K := K) (n := n)) :=
  Topology.IsInducing.induced _

instance : T1Space (PolynomialMatrixGroup K n) :=
  (show Topology.IsEmbedding (coordinates (K := K) (n := n)) from
    ⟨inducing_coordinates, coordinates_injective⟩).t1Space

instance : TopologicalSpace.NoetherianSpace (PolynomialMatrixGroup K n) :=
  inducing_coordinates.noetherianSpace

theorem continuous_of_polynomial {m : ℕ} (f : PolynomialMatrixGroup K n → PolynomialMatrixGroup K m)
    (p : Coord m → MvPolynomial (Coord n) K)
    (hp : ∀ g, coordinates (f g) = AffinePolynomialPoint.polynomialMap p (coordinates g)) :
    Continuous f := by
  apply inducing_coordinates.continuous_iff.mpr
  have he : coordinates ∘ f = AffinePolynomialPoint.polynomialMap p ∘ coordinates := funext hp
  rw [he]
  exact (AffinePolynomialPoint.continuous_polynomialMap p).comp inducing_coordinates.continuous

def leftPolynomial (h : PolynomialMatrixGroup K n) (s : Coord n) :
    MvPolynomial (Coord n) K :=
  if s.1 then
    ∑ k, MvPolynomial.X (true, s.2.1, k) * MvPolynomial.C (entries h⁻¹ k s.2.2)
  else
    ∑ k, MvPolynomial.C (entries h s.2.1 k) * MvPolynomial.X (false, k, s.2.2)

theorem coordinates_mul_left (h g : PolynomialMatrixGroup K n) :
    coordinates (h * g) =
      AffinePolynomialPoint.polynomialMap (leftPolynomial h) (coordinates g) := by
  apply AffinePolynomialPoint.ext
  funext ⟨b, i, j⟩
  cases b <;> simp [coordinates, AffinePolynomialPoint.polynomialMap,
    leftPolynomial, mul_inv_rev, Matrix.mul_apply]

def rightPolynomial (h : PolynomialMatrixGroup K n) (s : Coord n) :
    MvPolynomial (Coord n) K :=
  if s.1 then
    ∑ k, MvPolynomial.C (entries h⁻¹ s.2.1 k) * MvPolynomial.X (true, k, s.2.2)
  else
    ∑ k, MvPolynomial.X (false, s.2.1, k) * MvPolynomial.C (entries h k s.2.2)

theorem coordinates_mul_right (h g : PolynomialMatrixGroup K n) :
    coordinates (g * h) =
      AffinePolynomialPoint.polynomialMap (rightPolynomial h) (coordinates g) := by
  apply AffinePolynomialPoint.ext
  funext ⟨b, i, j⟩
  cases b <;> simp [coordinates, AffinePolynomialPoint.polynomialMap,
    rightPolynomial, mul_inv_rev, Matrix.mul_apply]

instance : SeparatelyContinuousMul (PolynomialMatrixGroup K n) where
  continuous_const_mul {h} := continuous_of_polynomial _ (leftPolynomial h) (coordinates_mul_left h)
  continuous_mul_const {h} := continuous_of_polynomial _ (rightPolynomial h) (coordinates_mul_right h)

instance : ContinuousInv (PolynomialMatrixGroup K n) where
  continuous_inv := by
    apply continuous_of_polynomial _ (fun s => MvPolynomial.X (!s.1, s.2.1, s.2.2))
    intro g
    apply AffinePolynomialPoint.ext
    funext ⟨b, i, j⟩
    cases b <;> simp [coordinates, AffinePolynomialPoint.polynomialMap]

end PolynomialMatrixGroup
end PolycyclicRecognition

end

end OAI
