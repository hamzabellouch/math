import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNormalizedNeighborStep
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialAutomorphismTopology
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanHeightRays
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanMeasuredConeHaar

namespace OAI

/-! # The same Cartan dilation in tiling, concentration, and source measure -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hbij : Function.Bijective F.ExpN)
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ v, chartN v = F.ExpN v)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)

/-- The continuous source dilation integrates the same Lie automorphism as
the algebraic dilation used by the stored linked chains. -/
def sourceDilation (h : H) : F.N.carrier ≃ₜ* F.N.carrier :=
  integrateNilpotentLieEquivContinuous F.N.equiv F.ExpN hbij chartN hchartN
    dynkinN F.isExpN M.bound_zero (cartanIdealWeightDilation T H h)

theorem sourceDilation_toMulEquiv (h : H) :
    (M.sourceDilation T F hbij chartN hchartN dynkinN h).toMulEquiv =
      integrateNilpotentLieEquiv F.N.equiv F.ExpN hbij dynkinN F.isExpN
        M.bound_zero (cartanIdealWeightDilation T H h) := rfl

theorem sourceDilation_apply_exp (h : H) (v : cartanRootIdeal H) :
    M.sourceDilation T F hbij chartN hchartN dynkinN h (F.ExpN (F.N.equiv v)) =
      F.ExpN (F.N.equiv (cartanIdealWeightDilation T H h v)) :=
  integrateNilpotentLieEquiv_apply_exp F.N.equiv F.ExpN hbij dynkinN F.isExpN
    M.bound_zero (cartanIdealWeightDilation T H h) v

/-- The normalized original step is the one used by this continuous
dilation, so the tiling identity requires no independent group action. -/
theorem sourceDilation_normalized_step (h : H) (i : Fin M.letterCount)
    (time : ℝ) (step : F.N.carrier)
    (hstep : F.inclusionN step = Exp (time •
      (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))) :
    (M.sourceDilation T F hbij chartN hchartN dynkinN h).symm step =
      F.ExpN (F.N.equiv ((Real.exp (-M.weight i h) * time) • M.letter i)) := by
  exact M.normalized_neighbor_step T F
    (fun h => (M.sourceDilation T F hbij chartN hchartN dynkinN h).toMulEquiv)
    (M.sourceDilation_apply_exp T F hbij chartN hchartN dynkinN) h i time step hstep

/-- Translating the polar templates to the inward contact point gives the
same dilation parameter as normalizing the neighboring letter. -/
theorem sourceDilation_inward_contact
    (eW : HeightSpace T.character ≃ₗ[ℝ] W) (w : W) (c δ r : ℝ) :
    (M.sourceDilation T F hbij chartN hchartN dynkinN
      ((r * (1 - c * δ)) • cartanHeightSection T H (eW.symm w))).toMulEquiv =
      integrateNilpotentLieEquiv F.N.equiv F.ExpN hbij dynkinN F.isExpN
        M.bound_zero (cartanIdealWeightDilation T H
          (r • cartanHeightSection T H (eW.symm ((1 - c * δ) • w)))) := by
  rw [map_smul, map_smul, smul_smul]
  rfl

/-- The canonical dilation preserves the product Haar measure for the
section selected by the source partition. -/
theorem sourceDilation_preserves_sectionMeasure
    (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
      LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
    (C : Set (H →ₗ[ℝ] ℝ)) (D : M.MeasuredCone F C)
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (σ : ContinuousMap D.Q.carrier F.N.carrier)
    (hσ : ∀ q, D.maps.quotient (σ q) = q) (h : H) :
    MeasureTheory.MeasurePreserving
      (M.sourceDilation T F hbij chartN hchartN dynkinN h)
      (D.sectionMeasure M F C σ hσ) (D.sectionMeasure M F C σ hσ) := by
  exact D.dilation_preserves_sectionMeasure M F C T hunimod haarN dynkinN hbij σ hσ h
    (M.sourceDilation T F hbij chartN hchartN dynkinN h)
    (M.sourceDilation_apply_exp T F hbij chartN hchartN dynkinN h)

end PolycyclicRecognition.CartanWordModel

end

end OAI
