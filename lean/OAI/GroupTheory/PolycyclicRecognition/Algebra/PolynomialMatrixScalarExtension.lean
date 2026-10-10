import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialMatrixStabilizer

namespace OAI

/-! # Faithful extension of scalars for concrete matrix groups -/

noncomputable section
namespace PolycyclicRecognition.PolynomialMatrixGroup

variable {K L : Type*} [Field K] [Field L] {n : ℕ}

def scalarExtension (f : K →+* L) : PolynomialMatrixGroup K n →* PolynomialMatrixGroup L n :=
  mulEquivGL.symm.toMonoidHom.comp ((Matrix.GeneralLinearGroup.map f).comp mulEquivGL.toMonoidHom)

@[simp] theorem scalarExtension_entries (f : K →+* L)
    (g : PolynomialMatrixGroup K n) (i j : Fin n) :
    entries (scalarExtension f g) i j = f (entries g i j) := rfl

theorem scalarExtension_injective (f : K →+* L) :
    Function.Injective (scalarExtension (n := n) f) := by
  intro g h he
  apply PolynomialMatrixGroup.ext
  apply Units.ext
  ext i j
  apply f.injective
  exact congrArg (fun a : PolynomialMatrixGroup L n => entries a i j) he

def scalarVector (f : K →+* L) : (Fin n → K) →+ (Fin n → L) where
  toFun v := fun i => f (v i)
  map_zero' := by ext i; exact f.map_zero
  map_add' v w := by ext i; exact f.map_add _ _

theorem scalarVector_injective (f : K →+* L) : Function.Injective (scalarVector (n := n) f) := by
  intro v w h
  funext i
  exact f.injective (congrFun h i)

theorem scalarVector_action (f : K →+* L) (g : PolynomialMatrixGroup K n) (v : Fin n → K) :
    scalarVector f (linearAction g v) = linearAction (scalarExtension f g) (scalarVector f v) := by
  ext i
  simp [scalarVector, linearAction_apply, Matrix.mulVec, dotProduct]

end PolycyclicRecognition.PolynomialMatrixGroup

end

end OAI
