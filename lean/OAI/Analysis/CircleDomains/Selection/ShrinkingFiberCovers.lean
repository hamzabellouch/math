import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

namespace OAI

/-! Covering a fiber by a shrinking family bounds its point count by the
lower limit of the number of covering images that contain the target. -/
open Set Function Filter MeasureTheory Metric
open scoped ENNReal Topology Classical
noncomputable section
namespace CircleDomainRigidity

lemma hausdorff_zero_fiber_le_liminf_cover
    {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y]
    (A : Set X) (f : X → Y) (r : ℕ → ℝ≥0∞) (hr : Tendsto r atTop (𝓝 0))
    (T : ℕ → ℕ → Set X) (hT : ∀ n k, ediam (T n k) ≤ r n)
    (hcover : ∀ n, A ⊆ ⋃ k, T n k) (y : Y) :
    (μH[0] : Measure X) (A ∩ f ⁻¹' {y}) ≤
      liminf (fun n => ∑' k, if y ∈ closure (f '' T n k) then (1 : ℝ≥0∞) else 0) atTop := by
  classical
  let I (n : ℕ) := {k : ℕ | (A ∩ f ⁻¹' {y} ∩ T n k).Nonempty}
  let S (n : ℕ) (k : I n) := A ∩ f ⁻¹' {y} ∩ T n k.val
  have hS : ∀ n k, ediam (S n k) ≤ r n := fun n k =>
    (ediam_mono inter_subset_right).trans (hT n k.val)
  have hcov : ∀ n, A ∩ f ⁻¹' {y} ⊆ ⋃ k : I n, S n k := by
    intro n x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hcover n hx.1)
    exact mem_iUnion.mpr ⟨⟨k, ⟨x, hx, hk⟩⟩, hx, hk⟩
  have h := Measure.hausdorffMeasure_le_liminf_tsum 0 (A ∩ f ⁻¹' {y}) r hr S
    (.of_forall hS) (.of_forall hcov)
  simp only [ENNReal.rpow_zero] at h
  apply h.trans
  apply liminf_le_liminf _ (by isBoundedDefault) (by isBoundedDefault)
  apply Eventually.of_forall
  intro n
  rw [show (∑' _ : I n, (1 : ℝ≥0∞)) = ∑' k, (I n).indicator (fun _ => (1 : ℝ≥0∞)) k from
    tsum_subtype (I n) (fun _ => (1 : ℝ≥0∞))]
  apply ENNReal.tsum_le_tsum
  intro k
  simp only [indicator_apply]
  split_ifs with hk hy
  · exact le_rfl
  · obtain ⟨x, hx, hxT⟩ := hk
    have hfxy : f x = y := hx.2
    exact False.elim (hy (subset_closure ⟨x, hxT, hfxy⟩))
  · exact zero_le
  · exact zero_le

end CircleDomainRigidity

end

end OAI
