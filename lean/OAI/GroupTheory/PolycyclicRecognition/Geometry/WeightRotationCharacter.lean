import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealCartanQuotient

namespace OAI

/-! # A compact rotation character on the actual adjoint-weight quotient -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : ComplexTriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

namespace ComplexTriangularAdjoint

/-- The rotations do not depend on the chosen Cartan representative. -/
theorem realPhaseVector_eq_of_weightMap_eq (h k : H)
    (hh : T.weightMap (h : L) = T.weightMap (k : L)) :
    realPhaseVector L H h = realPhaseVector L H k := by
  have hd : ((h - k : H) : L) ∈ T.kernelIdeal := by
    change T.weightMap ((h : L) - k) = 0
    rw [map_sub, hh, sub_self]
  have hn := complex_ad_nilpotent ((h - k : H) : L) (T.ad_nilpotent _ hd)
  have he : realCartanInComplex L H (h - k) =
      realCartanInComplex L H h - realCartanInComplex L H k := by
    apply Subtype.ext
    change (1 : ℂ) ⊗ₜ[ℝ] ((h : L) - k) = _
    exact TensorProduct.tmul_sub _ _ _
  apply Subtype.ext
  apply Subtype.ext
  funext χ
  have hz := χ.apply_eq_zero_of_isNilpotent (realCartanInComplex L H (h - k)) hn
  rw [he, map_sub, sub_eq_zero] at hz
  apply Subtype.ext
  change ComplexCartan.phase (complexifiedSubalgebra L H) (realCartanInComplex L H h) χ =
    ComplexCartan.phase (complexifiedSubalgebra L H) (realCartanInComplex L H k) χ
  unfold ComplexCartan.phase
  rw [hz]

/-- The rotational character on the image of the full complex adjoint
weight map, viewed as a real additive vector group. -/
def weightRotationCharacter : Multiplicative T.weightMap.range →* realRotationTorus L H :=
  (realPhaseHom L H).comp (T.cartanWeightSection H).toAddMonoidHom.toMultiplicative

/-- Compose the rotation character with a group-valued weight map. -/
def liftRotationCharacter {G : Type*} [Group G]
    (q : G →* Multiplicative T.weightMap.range) : G →* realRotationTorus L H :=
  (T.weightRotationCharacter H).comp q

@[simp] theorem weightRotationCharacter_cartan (h : H) :
    T.weightRotationCharacter H (Multiplicative.ofAdd (T.weightMap.rangeRestrict (h : L))) =
      realPhaseVector L H h := by
  apply T.realPhaseVector_eq_of_weightMap_eq H
  exact T.cartanWeightSection_weight H _

section Topology
variable [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]

local instance characterCartanTopologicalAddGroup : IsTopologicalAddGroup H :=
  Submodule.isTopologicalAddGroup H.toSubmodule

/-- The character is continuous for the actual finite-dimensional quotient
topology; no discrete replacement of the compact torus is used. -/
theorem continuous_weightRotationCharacter : Continuous (T.weightRotationCharacter H) :=
  (continuous_realPhaseVector L H).comp
    ((T.cartanWeightSection H).continuous_of_finiteDimensional.comp continuous_toAdd)

theorem continuous_liftRotationCharacter {G : Type*} [Group G] [TopologicalSpace G]
    (q : G →* Multiplicative T.weightMap.range) (hq : Continuous q) :
    Continuous (T.liftRotationCharacter H q) :=
  (T.continuous_weightRotationCharacter H).comp hq

end Topology
end ComplexTriangularAdjoint
end PolycyclicRecognition

end

end OAI
