import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanMeasuredConeHaar
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConeSourceCellVolumes
import Mathlib.MeasureTheory.Measure.Regular

namespace OAI

/-! # Positive compact probability cells for the actual cone models -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Set Metric TopologicalSpace
open scoped Manifold BigOperators

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (C : Set (H →ₗ[ℝ] ℝ)) (D : M.MeasuredCone F C)

/-- Replacing only the quotient Haar normalization leaves the intrinsic
kernel measure and its conjugation invariance intact. -/
def MeasuredCone.withQuotientHaar (μQ : Measure D.Q.carrier) (hμQ : μQ.IsHaarMeasure) :
    M.MeasuredCone F C where
  Q := D.Q
  I := D.I
  maps := D.maps
  measures := { D.measures with measureQ := μQ, haarQ := hμQ }

end PolycyclicRecognition.CartanWordModel

namespace PolycyclicRecognition

open MeasureTheory Set TopologicalSpace

/-- The original compact product cell supports the inner-regular probability
law used for concentration, with its unaltered product normalization. -/
theorem compact_product_cell_probability_data
    {Q K : Type*} [TopologicalSpace Q] [TopologicalSpace K]
    [PseudoMetrizableSpace Q] [PseudoMetrizableSpace K]
    [MeasurableSpace Q] [MeasurableSpace K] [BorelSpace Q] [BorelSpace K]
    [SecondCountableTopology Q] [SecondCountableTopology K]
    (μQ : Measure Q) (μK : Measure K) [SFinite μQ] [SFinite μK]
    (Z : Set Q) (J : Set K) (hZ : IsCompact Z) (hJ : IsCompact J)
    (hZ0 : μQ Z ≠ 0) (hZt : μQ Z ≠ ⊤) (hJ0 : μK J ≠ 0) (hJt : μK J ≠ ⊤) :
    (μQ.prod μK) (Z ×ˢ J) ≠ 0 ∧ (μQ.prod μK) (Z ×ˢ J) ≠ ⊤ ∧
      Nonempty (Z ×ˢ J) ∧
      ∀ ν : ProbabilityMeasure (Z ×ˢ J), (ν : Measure (Z ×ˢ J)).InnerRegular := by
  have h0 : (μQ.prod μK) (Z ×ˢ J) ≠ 0 := by
    rw [Measure.prod_prod]
    exact mul_ne_zero hZ0 hJ0
  have ht : (μQ.prod μK) (Z ×ˢ J) ≠ ⊤ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top hZt hJt
  refine ⟨h0, ht, Set.nonempty_coe_sort.mpr (nonempty_of_measure_ne_zero h0), ?_⟩
  intro ν
  let : CompactSpace (Z ×ˢ J) := isCompact_iff_compactSpace.mp (hZ.prod hJ)
  infer_instance

end PolycyclicRecognition

end

end OAI
