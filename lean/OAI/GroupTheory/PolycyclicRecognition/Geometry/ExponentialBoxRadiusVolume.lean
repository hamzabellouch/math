import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialSubsetVolume
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialBoxCoordinates

namespace OAI

/-! # Exact radius dependence of the original coordinate Haar boxes -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set
open scoped Manifold ENNReal

theorem exponential_box_radius_volume
    {L E G : Type*} [LieRing L] [LieAlgebra ℝ L]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace G] [ChartedSpace E G] [Group G]
    [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    {n : ℕ} (b₀ b : Basis (Fin n) ℝ L) {R : ℝ} (hR : 0 ≤ R) :
    (Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)
      (exponentialCoordinateBox (Exp ∘ e) b R) =
      ENNReal.ofReal R ^ n *
        (Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)
          (exponentialCoordinateBox (Exp ∘ e) b 1) := by
  rw [exponentialCoordinateBox_eq_cube_image _ _ R hR,
    exponentialCoordinateBox_eq_cube_image _ _ 1 zero_le_one,
    exponential_basis_subset_measure e Exp chart hchart,
    exponential_basis_subset_measure e Exp chart hchart]
  have hcube : volume (Icc (fun _ : Fin n => -R) (fun _ => R)) =
      ENNReal.ofReal R ^ n * volume (Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1)) := by
    simp only [Real.volume_Icc_pi, sub_neg_eq_add, ← two_mul,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), mul_pow]
    simp only [mul_one]
    exact mul_comm _ _
  rw [hcube]
  ac_rfl

end PolycyclicRecognition

end

end OAI
