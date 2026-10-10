import OAI.Analysis.CircleDomains.Selection.SmallHausdorffCovers
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

namespace OAI

/-! Diameter covers for codimension-one fibers. The estimate is also
useful on the critical set, where a positive chart Jacobian is unavailable. -/
open Set Function Filter MeasureTheory Metric
open scoped ENNReal Topology Classical
noncomputable section
namespace CircleDomainRigidity

lemma hausdorff_one_fiber_le_liminf_cover
    {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y]
    (A : Set X) (f : X → Y) (r : ℕ → ℝ≥0∞) (hr : Tendsto r atTop (𝓝 0))
    (T : ℕ → ℕ → Set X) (hT : ∀ n k, ediam (T n k) ≤ r n)
    (hcover : ∀ n, A ⊆ ⋃ k, T n k) (y : Y) :
    (μH[1] : Measure X) (A ∩ f ⁻¹' {y}) ≤
      liminf (fun n => ∑' k, if y ∈ closure (f '' T n k) then ediam (T n k) else 0) atTop := by
  let S (n k : ℕ) := A ∩ f ⁻¹' {y} ∩ T n k
  have hS : ∀ n k, ediam (S n k) ≤ r n := fun n k =>
    (ediam_mono inter_subset_right).trans (hT n k)
  have hcov : ∀ n, A ∩ f ⁻¹' {y} ⊆ ⋃ k, S n k := by
    intro n x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hcover n hx.1)
    exact mem_iUnion.mpr ⟨k, hx, hk⟩
  have h := Measure.hausdorffMeasure_le_liminf_tsum 1 (A ∩ f ⁻¹' {y}) r hr S
    (.of_forall hS) (.of_forall hcov)
  simp only [ENNReal.rpow_one] at h
  apply h.trans
  apply liminf_le_liminf _ (by isBoundedDefault) (by isBoundedDefault)
  apply Eventually.of_forall
  intro n
  apply ENNReal.tsum_le_tsum
  intro k
  split_ifs with hy
  · exact ediam_mono inter_subset_right
  · have hempty : S n k = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx, hxT⟩
      exact hy (subset_closure ⟨x, hxT, hx.2⟩)
    simp only [hempty, ediam_empty]
    exact le_rfl

lemma iSup_nonempty_ediam_sq {X : Type*} [EMetricSpace X] (S : Set X) :
    (⨆ _ : S.Nonempty, ediam S ^ (2 : ℝ)) = ediam S ^ (2 : ℝ) := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  · simp only [iSup_pos hS]

lemma exists_small_quadratic_hausdorff_cover
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (A : Set X) (hA : (μH[2] : Measure X) A < ∞)
    (r ε : ℝ≥0∞) (hr : 0 < r) (hε : 0 < ε) :
    ∃ T : ℕ → Set X, A ⊆ ⋃ k, T k ∧ (∀ k, ediam (T k) ≤ r) ∧
      (∑' k, ediam (T k) ^ (2 : ℕ)) < (μH[2] : Measure X) A + ε := by
  have hle : (⨅ (T : ℕ → Set X) (_ : A ⊆ ⋃ k, T k) (_ : ∀ k, ediam (T k) ≤ r),
      ∑' k, ⨆ _ : (T k).Nonempty, ediam (T k) ^ (2 : ℝ)) ≤ (μH[2] : Measure X) A := by
    rw [Measure.hausdorffMeasure_apply]
    exact le_iSup_of_le r (le_iSup_of_le hr le_rfl)
  have hlt := hle.trans_lt (ENNReal.lt_add_right hA.ne hε.ne')
  simp only [iInf_lt_iff] at hlt
  obtain ⟨T, hc, hd, hcost⟩ := hlt
  refine ⟨T, hc, hd, ?_⟩
  simp_rw [iSup_nonempty_ediam_sq] at hcost
  simpa only [ENNReal.rpow_two] using hcost

end CircleDomainRigidity

end

end OAI
