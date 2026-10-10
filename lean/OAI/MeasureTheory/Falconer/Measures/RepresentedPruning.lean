import OAI.MeasureTheory.Falconer.Radial.RadialCollisionDeletion

namespace OAI

/-! # Threshold deletion using one witness only on represented pin fibers -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem represented_threshold_pruning (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] (G : Set (X × Y)) (hG : MeasurableSet G)
    (K : X × Y → ℝ≥0∞) (hK : Measurable K) (F a : ℝ≥0∞)
    (hsmall : ∀ y, (∃ x, (x,y) ∈ G) → μ {x | (x,y) ∈ G ∧ F < K (x,y)} ≤ a) :
    ∃ H : Set (X × Y), MeasurableSet H ∧ H ⊆ G ∧
      (μ.prod ν) (G \ H) ≤ a*ν univ ∧ ∀ p ∈ H, K p ≤ F := by
  let H := G ∩ {p | K p ≤ F}
  have hH : MeasurableSet H := hG.inter (measurableSet_le hK measurable_const)
  refine ⟨H,hH,inter_subset_left,?_,fun p hp => hp.2⟩
  rw [Measure.prod_apply_symm (hG.diff hH)]
  apply (lintegral_mono _).trans_eq (lintegral_const a)
  intro y
  change μ {x | (x,y) ∈ G \ H} ≤ a
  by_cases hy : ∃ x, (x,y) ∈ G
  · apply (measure_mono _).trans (hsmall y hy)
    rintro x ⟨hx,hnot⟩
    exact ⟨hx,lt_of_not_ge (fun hk => hnot (show (x,y) ∈ H from ⟨hx,hk⟩))⟩
  · have he : {x | (x,y) ∈ G \ H} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      exact fun x hx => hy ⟨x,hx.1⟩
    rw [he,measure_empty]
    exact zero_le

end Falconer

end OAI
