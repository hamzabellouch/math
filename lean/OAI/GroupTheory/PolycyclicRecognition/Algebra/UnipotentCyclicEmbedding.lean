import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentPolynomialConjugation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.UnipotentLieFlow
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentSemidirectGroup
import OAI.GroupTheory.PolycyclicRecognition.Lattices.IntegerSemidirectLattice

namespace OAI

/-! # The actual integral subgroup in a nilpotent real cyclic extension -/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

abbrev PolynomialCyclicGroup (A : L ≃ₗ⁅ℝ⁆ L) :=
  L ⋊[integerPowerAction (PolynomialExponentialCoordinates.groupAutomorphism A)] Multiplicative ℤ

def unipotentCyclicEmbedding (A : L ≃ₗ⁅ℝ⁆ L)
    (hA : IsNilpotent (A.toLinearMap - 1)) :
    let D := unipotentLieLogarithm A hA
    let hD := unipotentLieLogarithm_nilpotent A hA
    letI := derivationSemidirectGroup D hD
    letI : MulOneClass (L × ℝ) := (derivationSemidirectGroup D hD).toMulOneClass
    PolynomialCyclicGroup A →* (L × ℝ) := by
  let D := unipotentLieLogarithm A hA
  let hD := unipotentLieLogarithm_nilpotent A hA
  let := derivationSemidirectGroup D hD
  let : Mul (L × ℝ) := (derivationSemidirectGroup D hD).toMul
  let : One (L × ℝ) := (derivationSemidirectGroup D hD).toOne
  let : Monoid (L × ℝ) := (derivationSemidirectGroup D hD).toMonoid
  let : MulOneClass (L × ℝ) := (derivationSemidirectGroup D hD).toMulOneClass
  let φ := PolynomialExponentialCoordinates.derivationAction D hD
  let a := PolynomialExponentialCoordinates.groupAutomorphism A
  have he (x : L) : (MonoidHom.id L) (a x) = φ (Multiplicative.ofAdd 1) ((MonoidHom.id L) x) := by
    change A x = unipotentLieFlow A hA 1 x
    rw [unipotentLieFlow_one]
  let e : (L × ℝ) ≃* (L ⋊[φ] Multiplicative ℝ) :=
    { derivationSemidirectEquiv D hD with map_mul' := fun _ _ => rfl }
  exact e.symm.toMonoidHom.comp (realIntegerSemidirectMap φ a (MonoidHom.id L) he)

@[simp] theorem unipotentCyclicEmbedding_apply (A : L ≃ₗ⁅ℝ⁆ L)
    (hA : IsNilpotent (A.toLinearMap - 1)) (z : PolynomialCyclicGroup A) :
    unipotentCyclicEmbedding A hA z = (z.left, (z.right.toAdd : ℝ)) := rfl

theorem unipotentCyclicEmbedding_injective (A : L ≃ₗ⁅ℝ⁆ L)
    (hA : IsNilpotent (A.toLinearMap - 1)) :
    Function.Injective (unipotentCyclicEmbedding A hA) := by
  intro x y h
  apply SemidirectProduct.ext
  · exact congrArg Prod.fst h
  · apply Multiplicative.ext
    have hh := congrArg Prod.snd h
    simp only [unipotentCyclicEmbedding_apply] at hh
    exact_mod_cast hh

end PolycyclicRecognition

end

end OAI
