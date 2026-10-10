import OAI.GroupTheory.PolycyclicRecognition.Algebra.ResidualLowerCentralLayers
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RelativeNilpotentExtension

namespace OAI

/-! # The actual joint-fixed residual extension is nilpotent

The quotient need not split. Its unipotent action has finite length on every
intrinsic Lie lower-central layer, and the cocycle disappears on those layers.
-/

noncomputable section
namespace PolycyclicRecognition
open LieModule
open scoped Manifold ContDiff IsMulCommutative
attribute [local instance] polynomialSubalgebraGroup
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q] [IsMulCommutative Q]
  {E : GroupExtension L G Q}
  {hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)} {qs : List Q}

namespace JointFixedReductionData
variable (D : JointFixedReductionData E hsmooth qs)

theorem residual_nilpotent (hgen : Subgroup.closure {q | q ∈ qs} = ⊤) :
    Group.IsNilpotent (FactorExtension D.residualSystem) := by
  let K := jointFixedLieSubalgebra D.operators
  let : LieRing.IsNilpotent K := Function.Injective.lieAlgebra_isNilpotent
    (f := K.incl) Subtype.val_injective
  obtain ⟨d, hd⟩ := (LieModule.isNilpotent_iff ℝ K K).mp
    (inferInstance : LieModule.IsNilpotent K K)
  have hbot : D.residualLayer d = ⊥ := by
    have hk : D.residualKernelLayer d = ⊥ := by
      apply eq_bot_iff.mpr
      intro x hx
      change x ∈ lowerCentralSeries ℝ K K d at hx
      rw [hd] at hx
      change x = 1
      exact hx.trans (Subtype.ext P.one_eq_zero).symm
    rw [residualLayer, hk, Subgroup.map_bot]
  have hzero : D.residualLayer 0 =
      (FactorExtension.groupExtension D.residualSystem).inl.range := by
    have hk : D.residualKernelLayer 0 = ⊤ := by
      ext x
      simp only [Subgroup.mem_top, iff_true]
      change x ∈ lowerCentralSeries ℝ K K 0
      simp
    rw [residualLayer, hk, Subgroup.map_top]
    rfl
  obtain ⟨c, hc⟩ := relative_series_descends_finite_layers ⊤ D.residualLayer
    (D.residualLayer_commutator_bound hgen) d
  apply nilpotent_of_relative_kernel_series (FactorExtension.groupExtension D.residualSystem) c
  rw [← hzero]
  exact eq_bot_iff.mpr (hbot ▸ hc)

end JointFixedReductionData
end PolycyclicRecognition

end

end OAI
