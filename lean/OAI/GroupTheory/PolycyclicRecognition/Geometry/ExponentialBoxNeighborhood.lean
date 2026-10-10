import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialBoxCompact
import Mathlib.MeasureTheory.Measure.OpenPos

namespace OAI

/-! # Positive Haar mass of exponential coordinate boxes -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory MeasureTheory.Measure Set Metric
open scoped Manifold Topology

variable {L E G : Type*} [LieRing L] [LieAlgebra ℝ L]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]
  (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
  (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)

include hchart hExp in
omit [T2Space G] in
theorem exponentialCoordinateBox_mem_nhds_one {n : ℕ} (b : Basis (Fin n) ℝ L)
    {R : ℝ} (hR : 0 < R) : exponentialCoordinateBox (Exp ∘ e) b R ∈ 𝓝 (1 : G) := by
  let f := (b.map e.toLinearEquiv).equivFunL.symm.toHomeomorph.trans chart
  have hf (x : Fin n → ℝ) : f x = Exp (e (b.equivFun.symm x)) := by
    simp only [f, Homeomorph.trans_apply, hchart]
    rfl
  have hf0 : f 0 = 1 := by rw [hf]; simp only [map_zero, hExp.map_zero]
  have hcube : Icc (fun _ : Fin n => -R) (fun _ => R) = closedBall 0 R := by
    ext x
    simp only [mem_Icc, Pi.le_def, mem_closedBall, dist_zero_right,
      pi_norm_le_iff_of_nonneg hR.le, Real.norm_eq_abs, abs_le]
    exact forall_and.symm
  rw [exponentialCoordinateBox_eq_cube_image _ _ _ hR.le]
  have he : (Exp ∘ e) ∘ b.equivFun.symm = f := by
    funext x
    exact (hf x).symm
  rw [he, hcube, ← hf0]
  exact f.isOpenMap.image_mem_nhds (closedBall_mem_nhds 0 hR)

variable [MeasurableSpace G] [BorelSpace G]

omit hExp [T2Space G] [MeasurableSpace G] [BorelSpace G] in
theorem exponentialCoordinateBox_nonempty {n : ℕ} (b : Basis (Fin n) ℝ L)
    {R : ℝ} (hR : 0 ≤ R) : (exponentialCoordinateBox (Exp ∘ e) b R).Nonempty :=
  ⟨(Exp ∘ e) 0, 0, rfl, by simpa only [map_zero, norm_zero] using hR⟩

include hchart hExp in
omit [T2Space G] [BorelSpace G] in
theorem exponentialCoordinateBox_measureReal_pos {n : ℕ} (b : Basis (Fin n) ℝ L)
    (μ : Measure G) [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]
    {R : ℝ} (hR : 0 < R) : 0 < μ.real (exponentialCoordinateBox (Exp ∘ e) b R) := by
  exact ENNReal.toReal_pos
    (measure_pos_of_mem_nhds μ (exponentialCoordinateBox_mem_nhds_one e Exp hExp chart hchart b hR)).ne'
    (isCompact_exponentialCoordinateBox e.toLinearEquiv Exp chart hchart b R hR.le).measure_ne_top

end PolycyclicRecognition

end

end OAI
