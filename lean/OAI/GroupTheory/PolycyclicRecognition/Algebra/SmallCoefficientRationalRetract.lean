import OAI.GroupTheory.PolycyclicRecognition.Analysis.SmallCoefficientRationalMean
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalTensorDimension

namespace OAI

/-! # Rational constants split off the rationalized bounded coefficient ring -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits MonoidalCategory ThompsonNonamenability
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G]

abbrev smallCoefficientRationalTensor : Rep ℤ G :=
  Rep.trivial ℤ G ℚ ⊗ smallCoefficientRepresentation G

theorem smallCoefficientRationalTensor_action (g : G)
    (x : smallCoefficientRationalTensor (G := G)) :
    (smallCoefficientRationalTensor (G := G)).ρ g x = smallCoefficientRationalAction g x := by
  induction x using TensorProduct.inductionOn with
  | tmul q b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

def smallCoefficientRationalConstants :
    Rep.trivial ℤ G ℚ ⟶ smallCoefficientRationalTensor (G := G) :=
  Rep.ofHom ⟨(TensorProduct.mk ℤ ℚ (SmallCoefficientRing G)).flip 1, fun g => by
    ext q
    change q ⊗ₜ[ℤ] (1 : SmallCoefficientRing G) = q ⊗ₜ[ℤ] (g • (1 : SmallCoefficientRing G))
    rw [smul_one]⟩

def smallCoefficientRationalRetract (M : InvariantMean G) :
    Retract (Rep.trivial ℤ G ℚ) (smallCoefficientRationalTensor (G := G)) := by
  let hmexists := exists_smallCoefficient_rational_mean M
  let m := Classical.choose hmexists
  have hm := (Classical.choose_spec hmexists).1
  have hinv := (Classical.choose_spec hmexists).2
  let r : smallCoefficientRationalTensor (G := G) ⟶ Rep.trivial ℤ G ℚ :=
    Rep.ofHom ⟨m.restrictScalars ℤ, fun g => by
      apply LinearMap.ext
      intro x
      change m ((smallCoefficientRationalTensor (G := G)).ρ g x) = m x
      rw [smallCoefficientRationalTensor_action, hinv]⟩
  refine ⟨smallCoefficientRationalConstants, r, ?_⟩
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  ext q
  change m (q ⊗ₜ[ℤ] (1 : SmallCoefficientRing G)) = q
  have he : q ⊗ₜ[ℤ] (1 : SmallCoefficientRing G) =
      q • ((1 : ℚ) ⊗ₜ[ℤ] (1 : SmallCoefficientRing G)) := by
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [he, map_smul, hm, smul_eq_mul, mul_one]

theorem rationalCoefficient_dimension_of_smallCoefficient [Countable G]
    (M : InvariantMean G) (d : ℕ)
    (hd : HasProjectiveDimensionLE (smallCoefficientRepresentation G) d) :
    HasProjectiveDimensionLE (Rep.trivial ℤ G ℚ) (d + 1) := by
  let := rationalTensor_left_dimension_le (smallCoefficientRepresentation G) d hd
  exact (smallCoefficientRationalRetract M).hasProjectiveDimensionLT (d + 2)

end PolycyclicRecognition

end

end OAI
