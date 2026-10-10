import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCellProbability
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialBoxRadiusVolume

namespace OAI

/-! # Positive finite probabilities and exact ratios for larger Cartan boxes -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Set
open scoped Manifold ENNReal

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

theorem groupBox_radius_properties
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases) (r : ℝ) {R : ℝ} (hR : 0 < R) :
    let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
    let Q := M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r R
    let C := M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r 1
    MeasurableSet Q ∧ μ Q ≠ 0 ∧ μ Q ≠ ∞ ∧
      μ Q / μ C = ENNReal.ofReal R ^ finrank ℝ (cartanRootIdeal H) := by
  dsimp only
  have hu := M.translated_groupBox_cell_properties T F hunimod eW
    haarN chartN hchartN b₀ E β r 1
  simp only [mul_one, image_id'] at hu
  have hv := exponential_box_radius_volume F.N.equiv F.ExpN chartN hchartN b₀
    (M.boxBasis T hunimod eW E β r) hR.le
  let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
  change μ (M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r R) =
    ENNReal.ofReal R ^ finrank ℝ (cartanRootIdeal H) *
      μ (M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r 1) at hv
  have hme := measurableEmbedding_translated_exponential_basis F.N.equiv F.ExpN
    chartN hchartN (M.boxBasis T hunimod eW E β r) 1
  simp only [mul_one] at hme
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [groupBox, exponentialCoordinateBox_eq_cube_image _ _ R hR.le]
    exact hme.measurableSet_image.mpr measurableSet_Icc
  · rw [hv]
    exact mul_ne_zero (pow_ne_zero _ (ENNReal.ofReal_pos.mpr hR).ne') hu.2.1
  · rw [hv]
    exact ENNReal.mul_ne_top (by simp) hu.2.2
  · rw [hv, ENNReal.mul_div_cancel_right hu.2.1 hu.2.2]

end PolycyclicRecognition.CartanWordModel

end

end OAI
