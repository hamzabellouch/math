import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.SeparatedSupportNets
import OAI.Analysis.RieszRectifiability.Packing.EuclideanPackingBound

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Module
open scoped ENNReal

theorem exists_separated_euclidean_closedBall_cover {k : ℕ} (R δ : ℝ) (hδ : 0 < δ) :
    ∃ s : Finset (Ambient k),
      (∀ x ∈ s, ‖x‖ ≤ R) ∧
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ dist x y) ∧
      (∀ x : Ambient k, ‖x‖ ≤ R → ∃ y ∈ s, dist x y < δ) := by
  classical
  obtain ⟨N, _, hNE, hsep, hcover⟩ := exists_separated_cover_extension
    (closedBall (0 : Ambient k) R) ∅ δ hδ (empty_subset _) (by simp)
  have hfinite : N.Finite := by
    have h := separated_set_finite_inter_compact N (closedBall (0 : Ambient k) R) δ hδ hsep
      (isCompact_closedBall 0 R)
    simpa only [inter_eq_left.mpr hNE] using! h
  refine ⟨hfinite.toFinset, ?_, ?_, ?_⟩
  · intro x hx
    have hm := hNE (hfinite.mem_toFinset.mp hx)
    simpa only [mem_closedBall, dist_zero_right] using! hm
  · intro x hx y hy hxy
    exact hsep (hfinite.mem_toFinset.mp hx) (hfinite.mem_toFinset.mp hy) hxy
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hcover x (by simpa only [mem_closedBall, dist_zero_right] using! hx)
    exact ⟨y, hfinite.mem_toFinset.mpr hy, hxy⟩

theorem euclidean_unit_ball_cover_card_lower {k : ℕ} (s : Finset (Ambient k))
    (δ : ℝ) (hδ : 0 < δ)
    (hcover : ∀ x : Ambient k, ‖x‖ < 1 → ∃ y ∈ s, dist x y < δ) :
    1 ≤ (s.card : ℝ) * δ ^ k := by
  let v : Measure (Ambient k) := volume
  have hsub : ball (0 : Ambient k) 1 ⊆ ⋃ y ∈ s, ball y δ := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hcover x (by simpa only [mem_ball, dist_zero_right] using! hx)
    exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hy, hxy⟩⟩
  have hb : v (ball 0 1) ≤ (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ k) * v (ball 0 1) := by
    calc
      _ ≤ v (⋃ y ∈ s, ball y δ) := measure_mono hsub
      _ ≤ ∑ y ∈ s, v (ball y δ) := measure_biUnion_finset_le s _
      _ = _ := by
        simp only [v.addHaar_ball_of_pos _ hδ, finrank_euclideanSpace_fin,
          Finset.sum_const, nsmul_eq_mul, mul_assoc]
  have hi : (1 : ℝ≥0∞) ≤ (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ k) := by
    apply (ENNReal.mul_le_mul_iff_left (measure_ball_pos v 0 zero_lt_one).ne'
      (measure_ball_lt_top (μ := v) (x := 0) (r := 1)).ne).mp
    simpa only [one_mul] using! hb
  have hfin : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ k) ≠ ∞ := by finiteness
  have hreal := ENNReal.toReal_mono hfin hi
  simpa only [ENNReal.toReal_one, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (pow_nonneg hδ.le k)] using! hreal

end

end RieszRectifiability

end OAI
