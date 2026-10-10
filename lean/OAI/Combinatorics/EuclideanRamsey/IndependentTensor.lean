import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.MvPolynomial

namespace OAI

noncomputable section
open scoped TensorProduct

namespace EuclideanRamsey.IndependentTensor

universe u
variable (ι : Type u)

abbrev Poly := MvPolynomial ι ℚ
abbrev Rat := FractionRing (Poly ι)
abbrev JointPoly := MvPolynomial (ι ⊕ ι) ℚ
abbrev JointField := FractionRing (JointPoly ι)

def polyToRat : Poly ι →ₐ[ℚ] Rat ι :=
  IsScalarTower.toAlgHom ℚ (Poly ι) (Rat ι)

def jointToField : JointPoly ι →ₐ[ℚ] JointField ι :=
  IsScalarTower.toAlgHom ℚ (JointPoly ι) (JointField ι)

def leftPolynomialMap : Poly ι →ₐ[ℚ] JointField ι :=
  (jointToField ι).comp (MvPolynomial.rename Sum.inl)

def rightPolynomialMap : Poly ι →ₐ[ℚ] JointField ι :=
  (jointToField ι).comp (MvPolynomial.rename Sum.inr)

theorem leftPolynomialMap_injective :
    Function.Injective (leftPolynomialMap ι) :=
  (IsFractionRing.injective (JointPoly ι) (JointField ι)).comp
    (MvPolynomial.rename_injective Sum.inl Sum.inl_injective)

theorem rightPolynomialMap_injective :
    Function.Injective (rightPolynomialMap ι) :=
  (IsFractionRing.injective (JointPoly ι) (JointField ι)).comp
    (MvPolynomial.rename_injective Sum.inr Sum.inr_injective)

/-- The first rational-function copy, in the independent left variables. -/
def leftMap : Rat ι →ₐ[ℚ] JointField ι :=
  IsFractionRing.liftAlgHom (K := Rat ι) (leftPolynomialMap_injective ι)

/-- The second rational-function copy, in the independent right variables. -/
def rightMap : Rat ι →ₐ[ℚ] JointField ι :=
  IsFractionRing.liftAlgHom (K := Rat ι) (rightPolynomialMap_injective ι)

@[simp] theorem leftMap_algebraMap (p : Poly ι) :
    leftMap ι (algebraMap (Poly ι) (Rat ι) p) =
      algebraMap (JointPoly ι) (JointField ι) (MvPolynomial.rename Sum.inl p) := by
  exact IsFractionRing.lift_algebraMap (K := Rat ι)
    (g := (leftPolynomialMap ι).toRingHom) (leftPolynomialMap_injective ι) p

@[simp] theorem rightMap_algebraMap (p : Poly ι) :
    rightMap ι (algebraMap (Poly ι) (Rat ι) p) =
      algebraMap (JointPoly ι) (JointField ι) (MvPolynomial.rename Sum.inr p) := by
  exact IsFractionRing.lift_algebraMap (K := Rat ι)
    (g := (rightPolynomialMap ι).toRingHom) (rightPolynomialMap_injective ι) p

@[simp] theorem leftMap_X (i : ι) :
    leftMap ι (algebraMap (Poly ι) (Rat ι) (MvPolynomial.X i)) =
      algebraMap (JointPoly ι) (JointField ι) (MvPolynomial.X (Sum.inl i)) := by
  simp

@[simp] theorem rightMap_X (i : ι) :
    rightMap ι (algebraMap (Poly ι) (Rat ι) (MvPolynomial.X i)) =
      algebraMap (JointPoly ι) (JointField ι) (MvPolynomial.X (Sum.inr i)) := by
  simp

/-- The map to the joint rational-function field. -/
def tensorEmbedding : Rat ι ⊗[ℚ] Rat ι →ₐ[ℚ] JointField ι :=
  Algebra.TensorProduct.lift (leftMap ι) (rightMap ι) (fun _ _ => Commute.all _ _)

@[simp] theorem tensorEmbedding_tmul (x y : Rat ι) :
    tensorEmbedding ι (x ⊗ₜ[ℚ] y) = leftMap ι x * rightMap ι y := by
  rfl

@[simp] theorem tensorEmbedding_X_tmul_one (i : ι) :
    tensorEmbedding ι
      ((algebraMap (Poly ι) (Rat ι) (MvPolynomial.X i)) ⊗ₜ[ℚ] 1) =
      algebraMap (JointPoly ι) (JointField ι) (MvPolynomial.X (Sum.inl i)) := by
  simp

@[simp] theorem tensorEmbedding_one_tmul_X (i : ι) :
    tensorEmbedding ι
      (1 ⊗ₜ[ℚ] (algebraMap (Poly ι) (Rat ι) (MvPolynomial.X i))) =
      algebraMap (JointPoly ι) (JointField ι) (MvPolynomial.X (Sum.inr i)) := by
  simp

def localizeLeft : Poly ι ⊗[ℚ] Poly ι →ₐ[ℚ] Rat ι ⊗[ℚ] Poly ι :=
  Algebra.TensorProduct.map (polyToRat ι) (AlgHom.id ℚ (Poly ι))

def localizeRight : Rat ι ⊗[ℚ] Poly ι →ₐ[ℚ] Rat ι ⊗[ℚ] Rat ι :=
  Algebra.TensorProduct.map (AlgHom.id ℚ (Rat ι)) (polyToRat ι)

def halfEmbedding : Rat ι ⊗[ℚ] Poly ι →ₐ[ℚ] JointField ι :=
  (tensorEmbedding ι).comp (localizeRight ι)

def polynomialEmbedding : Poly ι ⊗[ℚ] Poly ι →ₐ[ℚ] JointField ι :=
  (jointToField ι).comp (MvPolynomial.tensorEquivSum ℚ ι ι ℚ).toAlgHom

theorem polynomialEmbedding_injective :
    Function.Injective (polynomialEmbedding ι) :=
  (IsFractionRing.injective (JointPoly ι) (JointField ι)).comp
    (MvPolynomial.tensorEquivSum ℚ ι ι ℚ).injective

/-- On polynomials the joint map is the standard polynomial tensor equivalence,
followed by the injective fraction-ring inclusion. -/
theorem halfEmbedding_comp_localizeLeft :
    (halfEmbedding ι).comp (localizeLeft ι) = polynomialEmbedding ι := by
  apply Algebra.TensorProduct.ext
  · ext i
    simp [halfEmbedding, localizeLeft, localizeRight, polyToRat,
      polynomialEmbedding, jointToField, IsScalarTower.toAlgHom_apply]
  · ext i
    simp [halfEmbedding, localizeLeft, localizeRight, polyToRat,
      polynomialEmbedding, jointToField, IsScalarTower.toAlgHom_apply]

/-- First localization: invert all nonzero polynomials in the left factor.
The target map detects zero on the polynomial base, hence on its localization. -/
theorem halfEmbedding_injective : Function.Injective (halfEmbedding ι) := by
  let : Algebra (Poly ι ⊗[ℚ] Poly ι) (Rat ι ⊗[ℚ] Poly ι) :=
    (localizeLeft ι).toAlgebra
  let : IsScalarTower (Poly ι) (Poly ι ⊗[ℚ] Poly ι) (Rat ι ⊗[ℚ] Poly ι) :=
    IsScalarTower.of_algebraMap_eq
      (R := Poly ι) (S := Poly ι ⊗[ℚ] Poly ι) (A := Rat ι ⊗[ℚ] Poly ι) (by
      intro p
      change algebraMap (Poly ι) (Rat ι) p ⊗ₜ[ℚ] (1 : Poly ι) =
        localizeLeft ι (p ⊗ₜ[ℚ] (1 : Poly ι))
      simp [localizeLeft, polyToRat, IsScalarTower.toAlgHom_apply])
  have hcompat :
      (algebraMap (Poly ι ⊗[ℚ] Poly ι) (Rat ι ⊗[ℚ] Poly ι)).comp
          Algebra.TensorProduct.includeRight.toRingHom =
        Algebra.TensorProduct.includeRight.toRingHom := by
    apply RingHom.ext
    intro p
    change localizeLeft ι ((1 : Poly ι) ⊗ₜ[ℚ] p) = (1 : Rat ι) ⊗ₜ[ℚ] p
    simp [localizeLeft, polyToRat, IsScalarTower.toAlgHom_apply]
  let : IsLocalization
      (Algebra.algebraMapSubmonoid (Poly ι ⊗[ℚ] Poly ι) (nonZeroDivisors (Poly ι)))
      (Rat ι ⊗[ℚ] Poly ι) :=
    IsLocalization.tensorProduct_tensorProduct ℚ (Poly ι)
      (nonZeroDivisors (Poly ι)) (Rat ι) hcompat
  apply IsLocalization.injective_of_map_algebraMap_zero
    (M := Algebra.algebraMapSubmonoid (Poly ι ⊗[ℚ] Poly ι) (nonZeroDivisors (Poly ι)))
    (S := Rat ι ⊗[ℚ] Poly ι)
    (halfEmbedding ι).toRingHom
  intro x hx
  have hbase : polynomialEmbedding ι x = 0 := by
    have heq := AlgHom.congr_fun (halfEmbedding_comp_localizeLeft ι) x
    simpa only [AlgHom.comp_apply, RingHom.algebraMap_toAlgebra] using
      heq.symm.trans hx
  have hxzero : x = 0 := (polynomialEmbedding_injective ι)
    (hbase.trans (map_zero (polynomialEmbedding ι)).symm)
  simp [hxzero]

/-- The two independent rational-function copies embed faithfully. -/
theorem tensorEmbedding_injective : Function.Injective (tensorEmbedding ι) := by
  let : Algebra (Rat ι ⊗[ℚ] Poly ι) (Rat ι ⊗[ℚ] Rat ι) :=
    (localizeRight ι).toAlgebra
  let : IsScalarTower (Rat ι) (Rat ι ⊗[ℚ] Poly ι) (Rat ι ⊗[ℚ] Rat ι) :=
    IsScalarTower.of_algebraMap_eq
      (R := Rat ι) (S := Rat ι ⊗[ℚ] Poly ι) (A := Rat ι ⊗[ℚ] Rat ι) (by
      intro x
      change x ⊗ₜ[ℚ] (1 : Rat ι) =
        localizeRight ι (x ⊗ₜ[ℚ] (1 : Poly ι))
      simp [localizeRight, polyToRat, IsScalarTower.toAlgHom_apply])
  have hcompat :
      (algebraMap (Rat ι ⊗[ℚ] Poly ι) (Rat ι ⊗[ℚ] Rat ι)).comp
          Algebra.TensorProduct.includeRight.toRingHom =
        Algebra.TensorProduct.includeRight.toRingHom.comp
          (algebraMap (Poly ι) (Rat ι)) := by
    apply RingHom.ext
    intro p
    change localizeRight ι ((1 : Rat ι) ⊗ₜ[ℚ] p) =
      (1 : Rat ι) ⊗ₜ[ℚ] algebraMap (Poly ι) (Rat ι) p
    simp [localizeRight, polyToRat, IsScalarTower.toAlgHom_apply]
  let : IsLocalization
      ((nonZeroDivisors (Poly ι)).map
        (Algebra.TensorProduct.includeRight (R := ℚ) (A := Rat ι)))
      (Rat ι ⊗[ℚ] Rat ι) :=
    IsLocalization.tensorProduct_tensorProduct_right ℚ (Rat ι)
      (nonZeroDivisors (Poly ι)) (Rat ι) hcompat
  apply IsLocalization.injective_of_map_algebraMap_zero
    (M := (nonZeroDivisors (Poly ι)).map
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := Rat ι)))
    (S := Rat ι ⊗[ℚ] Rat ι)
    (tensorEmbedding ι).toRingHom
  intro x hx
  have hhalf : halfEmbedding ι x = 0 := by
    change halfEmbedding ι x = 0 at hx
    exact hx
  have hxzero : x = 0 := (halfEmbedding_injective ι)
    (hhalf.trans (map_zero (halfEmbedding ι)).symm)
  simp [hxzero]

end EuclideanRamsey.IndependentTensor

end

end OAI
