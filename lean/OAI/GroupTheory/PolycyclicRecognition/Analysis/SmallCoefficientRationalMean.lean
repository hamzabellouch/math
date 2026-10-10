import OAI.GroupTheory.PolycyclicRecognition.Analysis.SmallCoefficientMean
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalExteriorHomology
import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace OAI

/-! # An invariant rational functional on the rationalized coefficient ring

The real mean proves that the constant class is nonzero in coinvariants.
Linear separation over the rationals then supplies a rational functional;
no rational-valued positive mean on all bounded functions is assumed.
-/
noncomputable section
namespace PolycyclicRecognition
open ThompsonNonamenability Representation
open scoped TensorProduct
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G]

abbrev SmallCoefficientRationalSpace := ℚ ⊗[ℤ] SmallCoefficientRing G

def smallCoefficientRationalAction : Representation ℚ G (SmallCoefficientRationalSpace (G := G)) where
  toFun g := ((smallCoefficientRepresentation G).ρ g).baseChange ℚ
  map_one' := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro q b
    change q ⊗ₜ[ℤ] ((smallCoefficientRepresentation G).ρ 1 b) = q ⊗ₜ[ℤ] b
    rw [map_one]
    rfl
  map_mul' g h := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro q b
    change q ⊗ₜ[ℤ] ((smallCoefficientRepresentation G).ρ (g * h) b) =
      q ⊗ₜ[ℤ] ((smallCoefficientRepresentation G).ρ g ((smallCoefficientRepresentation G).ρ h b))
    rw [map_mul]
    rfl

def smallCoefficientRationalRealMean (M : InvariantMean G) :
    SmallCoefficientRationalSpace (G := G) →ₗ[ℚ] ℝ :=
  rationalLinearExtension (smallCoefficientRealMean M)

theorem smallCoefficientRationalRealMean_invariant (M : InvariantMean G) (g : G) :
    (smallCoefficientRationalRealMean M).comp (smallCoefficientRationalAction g) =
      smallCoefficientRationalRealMean M := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro q b
  change q • smallCoefficientRealMean M (g • b) = q • smallCoefficientRealMean M b
  rw [smallCoefficientRealMean_invariant]

def smallCoefficientRealCoinvariantMean (M : InvariantMean G) :
    Coinvariants (smallCoefficientRationalAction (G := G)) →ₗ[ℚ] ℝ :=
  Coinvariants.lift _ (smallCoefficientRationalRealMean M)
    (smallCoefficientRationalRealMean_invariant M)

@[simp]
theorem smallCoefficientRealCoinvariantMean_one (M : InvariantMean G) :
    smallCoefficientRealCoinvariantMean M
      (Coinvariants.mk smallCoefficientRationalAction
        ((1 : ℚ) ⊗ₜ[ℤ] (1 : SmallCoefficientRing G))) = 1 := by
  change (1 : ℚ) • smallCoefficientRealMean M 1 = 1
  rw [smallCoefficientRealMean_one, one_smul]

theorem exists_smallCoefficient_rational_mean (M : InvariantMean G) :
    ∃ m : SmallCoefficientRationalSpace (G := G) →ₗ[ℚ] ℚ,
      m ((1 : ℚ) ⊗ₜ[ℤ] (1 : SmallCoefficientRing G)) = 1 ∧
      ∀ (g : G) (x : SmallCoefficientRationalSpace (G := G)),
        m (smallCoefficientRationalAction g x) = m x := by
  let u := Coinvariants.mk smallCoefficientRationalAction
    ((1 : ℚ) ⊗ₜ[ℤ] (1 : SmallCoefficientRing G))
  have hu : u ≠ 0 := by
    intro h
    have hm := smallCoefficientRealCoinvariantMean_one M
    change smallCoefficientRealCoinvariantMean M u = 1 at hm
    rw [h, map_zero] at hm
    exact zero_ne_one hm
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℚ hu
  refine ⟨f.comp (Coinvariants.mk smallCoefficientRationalAction), hf, ?_⟩
  intro g x
  change f (Coinvariants.mk smallCoefficientRationalAction (smallCoefficientRationalAction g x)) =
    f (Coinvariants.mk smallCoefficientRationalAction x)
  rw [Coinvariants.mk_self_apply]

end PolycyclicRecognition

end

end OAI
