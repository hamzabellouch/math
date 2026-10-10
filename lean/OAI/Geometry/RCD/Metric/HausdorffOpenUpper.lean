import OAI.Geometry.RCD.Metric.EuclideanFineBallCover
import OAI.Geometry.RCD.Metric.EuclideanBallHausdorffCost
import OAI.Geometry.RCD.Metric.HausdorffAlmostCover

namespace OAI

/-! # Sharp Hausdorff upper bounds on Euclidean open sets -/

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem raw_hausdorff_open_upper {n : ℕ} (hn : 0 < n)
    {U : Set (Euclidean n)} (hU : IsOpen U) :
    Measure.hausdorffMeasure (n:ℝ) U ≤
      ((2:ℝ≥0∞)^n/volume (ball (0 : Euclidean n) 1))*volume U := by
  apply hausdorff_le_of_ae_small_covers
  intro δ hδ
  have hη : ∃ η : ℝ, 0 < η ∧ ENNReal.ofReal (2*η) ≤ δ := by
    by_cases hd : δ=⊤
    · exact ⟨1,zero_lt_one,by simp only [hd,le_top]⟩
    have h0 := ENNReal.toReal_pos hδ.ne' hd
    refine ⟨δ.toReal/4,by positivity,?_⟩
    calc
      ENNReal.ofReal (2*(δ.toReal/4)) ≤ ENNReal.ofReal δ.toReal :=
        ENNReal.ofReal_le_ofReal (by linarith only [h0])
      _ = δ := ENNReal.ofReal_toReal hd
  obtain ⟨η,hη,hηδ⟩ := hη
  obtain ⟨J,hcount,hJ,hdisj,hcov⟩ := euclidean_fine_ball_cover hn hU hη
  let : Countable J := hcount.to_subtype
  let B := fun z : J => closedBall z.val.1 z.val.2
  have hsub : (⋃ z : J, B z) ⊆ U := iUnion_subset fun z => (hJ z.val z.property).2.2
  have hpair : Pairwise (fun z w => Disjoint (B z) (B w)) := by
    intro z w hzw
    exact hdisj z.property w.property (Subtype.val_injective.ne hzw)
  have hmass : (∑' z : J, volume (B z)) ≤ volume U := by
    rw [← measure_iUnion hpair (fun _ => measurableSet_closedBall)]
    exact measure_mono hsub
  refine ⟨J,inferInstance,B,?_,?_,?_⟩
  · intro z
    exact (closedBall_ediam_le_twice z.val.1 z.val.2).trans
      ((ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hJ z.val z.property).2.1
        (by norm_num))).trans hηδ)
  · apply raw_hausdorff_absolutelyContinuous
    simpa only [B,biUnion_eq_iUnion] using hcov
  · calc
      (∑' z : J, ediam (B z)^(n:ℝ)) ≤ ∑' z : J,
          ((2:ℝ≥0∞)^n/volume (ball (0 : Euclidean n) 1))*volume (B z) :=
        ENNReal.tsum_le_tsum fun z => euclidean_ball_diameter_cost hn z.val.1 (hJ z.val z.property).1
      _ = ((2:ℝ≥0∞)^n/volume (ball (0 : Euclidean n) 1))*(∑' z : J, volume (B z)) :=
        ENNReal.tsum_mul_left
      _ ≤ _ := by gcongr

end RegularPointCoordinates

end

end OAI
