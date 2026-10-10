import OAI.NumberTheory.Ostmann.Arithmetic.BulkIntegrands

namespace OAI

/-! # Reassembling log cells with the original normalization -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

noncomputable def bulkCellMixture {C : Type*} [Fintype C]
    (Z : ℝ) (μ : C → Measure ℝ) : Measure ℝ := ENNReal.ofReal Z • ∑ c, μ c

instance finite_bulkCellMixture {C : Type*} [Fintype C]
    (Z : ℝ) (μ : C → Measure ℝ) [∀ c, IsFiniteMeasure (μ c)] :
    IsFiniteMeasure (bulkCellMixture Z μ) := by
  unfold bulkCellMixture
  exact (∑ c, μ c).smul_finite ENNReal.ofReal_ne_top

theorem BulkIntegrand.average_cellMixture {σ C : Type*} [Fintype σ] [Fintype C]
    (f : BulkIntegrand σ) (Z : ℝ) (hZ : 0 ≤ Z)
    (μ : C → Measure ℝ) [∀ c, IsFiniteMeasure (μ c)] (i : σ) (x : σ → ℝ) :
    f.average (bulkCellMixture Z μ) i x = (Z : ℂ) * ∑ c, f.average (μ c) i x := by
  change (∫ t, f (Function.update x i t) ∂bulkCellMixture Z μ) = _
  rw [bulkCellMixture, integral_smul_measure, ENNReal.toReal_ofReal hZ,
    integral_finsetSum_measure]
  · rfl
  · intro c _
    exact f.slice_integrable (μ c) i x

/-- Cell counts multiply only the approximation error. The original
normalization is applied to both the prime and Page cell measures. -/
theorem BulkIntegrand.cellMixture_comparison {σ C : Type*} [Fintype σ] [Fintype C]
    (f : BulkIntegrand σ) (Z : ℝ) (hZ : 0 ≤ Z)
    (μ ν : C → Measure ℝ) [∀ c, IsFiniteMeasure (μ c)] [∀ c, IsFiniteMeasure (ν c)]
    (i : σ) (ε : C → ℝ)
    (hε : ∀ c x, ‖f.average (μ c) i x - f.average (ν c) i x‖ ≤ ε c) (x : σ → ℝ) :
    ‖f.average (bulkCellMixture Z μ) i x - f.average (bulkCellMixture Z ν) i x‖ ≤
      Z * ∑ c, ε c := by
  rw [f.average_cellMixture Z hZ, f.average_cellMixture Z hZ, ← mul_sub,
    ← Finset.sum_sub_distrib, norm_mul, Complex.norm_real, Real.norm_of_nonneg hZ]
  apply mul_le_mul_of_nonneg_left _ hZ
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => hε c x)

/-- Joint cell reassembly uses bounded normalized masses, without inserting
cell counts into the main term. -/
theorem BulkIntegrand.cellMixtures_joint_comparison {σ C : Type*} [Fintype σ] [Fintype C]
    (f : BulkIntegrand σ) (Z : σ → ℝ) (hZ : ∀ i, 0 ≤ Z i)
    (μ ν : σ → C → Measure ℝ)
    [∀ i c, IsFiniteMeasure (μ i c)] [∀ i c, IsFiniteMeasure (ν i c)]
    (order : List σ) (horder : order.Nodup)
    (hμ : ∀ i ∈ order, (bulkCellMixture (Z i) (μ i)).real Set.univ ≤ 2)
    (hν : ∀ i ∈ order, (bulkCellMixture (Z i) (ν i)).real Set.univ ≤ 2)
    (ε : σ → C → ℝ) (hε : ∀ i ∈ order, ∀ c, 0 ≤ ε i c)
    (herr : ∀ i ∈ order, ∀ c x,
      ‖f.average (μ i c) i x - f.average (ν i c) i x‖ ≤ ε i c) :
    ∀ x, ‖f.averages (fun i => bulkCellMixture (Z i) (μ i)) order x -
      f.averages (fun i => bulkCellMixture (Z i) (ν i)) order x‖ ≤
      2 ^ order.length * (order.map (fun i => Z i * ∑ c, ε i c)).sum := by
  apply f.averages_comparison _ _ order horder hμ hν
  · intro i hi
    exact mul_nonneg (hZ i) (Finset.sum_nonneg fun c _ => hε i hi c)
  · intro i hi x
    exact f.cellMixture_comparison (Z i) (hZ i) (μ i) (ν i) i (ε i) (herr i hi) x

end Ostmann

end OAI
