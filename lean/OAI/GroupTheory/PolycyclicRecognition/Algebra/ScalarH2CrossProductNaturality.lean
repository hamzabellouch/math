import OAI.GroupTheory.PolycyclicRecognition.Algebra.ScalarH2BilinearDetection
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ExteriorSquareHomologyNaturality

namespace OAI

/-! # Naturality of the scalar-extended second-homology cross product -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable (K : Type) [Field K] {A B : Type} [CommGroup A] [CommGroup B]

theorem scalarExtendedH2Pairing_natural (f : A →* B)
    (x y : K ⊗[ℤ] Additive A) :
    ((groupHomology.map f (integralTrivialCoefficientMap f) 2).hom.baseChange K)
        (scalarExtendedH2Pairing K A x y) =
      scalarExtendedH2Pairing K B
        (((additiveGroupLinearMap f).baseChange K) x)
        (((additiveGroupLinearMap f).baseChange K) y) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    induction y using TensorProduct.inductionOn with
    | tmul s b =>
      rw [scalarExtendedH2Pairing_tmul, map_smul]
      change (r * s) • ((1 : K) ⊗ₜ[ℤ]
        groupHomology.map f (integralTrivialCoefficientMap f) 2 (abelianH2Class a.toMul b.toMul)) =
          scalarExtendedH2Pairing K B (r ⊗ₜ[ℤ] Additive.ofMul (f a.toMul))
            (s ⊗ₜ[ℤ] Additive.ofMul (f b.toMul))
      rw [abelianH2Class_natural, scalarExtendedH2Pairing_tmul]
      rfl
    | add y z hy hz => simp only [map_add, hy, hz]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]

theorem scalarExtendedH2ExteriorProduct_natural (f : A →* B) :
    ((groupHomology.map f (integralTrivialCoefficientMap f) 2).hom.baseChange K).comp
        (scalarExtendedH2ExteriorProduct K A) =
      (scalarExtendedH2ExteriorProduct K B).comp
        (exteriorPower.map 2 ((additiveGroupLinearMap f).baseChange K)) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply]
  rw [hv, scalarExtendedH2ExteriorProduct_value, scalarExtendedH2Pairing_natural,
    exteriorPower.map_apply_ιMulti]
  have he : ⇑((additiveGroupLinearMap f).baseChange K) ∘ ![v 0, v 1] =
      ![(additiveGroupLinearMap f).baseChange K (v 0),
        (additiveGroupLinearMap f).baseChange K (v 1)] := by
    ext i
    fin_cases i <;> rfl
  rw [he, scalarExtendedH2ExteriorProduct_value]

end PolycyclicRecognition

end

end OAI
