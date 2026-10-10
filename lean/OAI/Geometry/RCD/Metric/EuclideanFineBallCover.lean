import OAI.Geometry.RCD.Sobolev.EuclideanEnergyRatios
import Mathlib.MeasureTheory.Covering.Vitali

namespace OAI

/-! # Arbitrarily fine disjoint closed-ball covers of Euclidean open sets -/

open Set Metric MeasureTheory
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates

theorem euclidean_fine_ball_cover {n : ℕ} (hn : 0 < n)
    {U : Set (Euclidean n)} (hU : IsOpen U) {η : ℝ} (hη : 0 < η) :
    ∃ J : Set (Euclidean n × ℝ), J.Countable ∧
      (∀ z ∈ J, 0 < z.2 ∧ z.2 ≤ η ∧ closedBall z.1 z.2 ⊆ U) ∧
      J.PairwiseDisjoint (fun z => closedBall z.1 z.2) ∧
      volume (U \ ⋃ z ∈ J, closedBall z.1 z.2)=0 := by
  let : NeZero n := ⟨hn.ne'⟩
  let T : Set (Euclidean n × ℝ) := {z | 0 < z.2 ∧ z.2 ≤ η ∧ closedBall z.1 z.2 ⊆ U}
  have hdouble (z : Euclidean n × ℝ) (_hz : z ∈ T) :
      volume (closedBall z.1 (3*z.2)) ≤ (3^n : ℝ≥0)*volume (closedBall z.1 z.2) := by
    rw [Measure.addHaar_closedBall_mul_of_pos volume z.1 (by norm_num : (0:ℝ)<3)]
    rw [Measure.addHaar_closedBall_center volume z.1]
    simp only [finrank_euclideanSpace_fin,ENNReal.coe_pow,ENNReal.coe_ofNat,
      ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤3),ENNReal.ofReal_ofNat,le_refl]
  have hf (x : Euclidean n) (hx : x ∈ U) (ε : ℝ) (hε : 0 < ε) :
      ∃ z ∈ T, z.2 ≤ ε ∧ z.1=x := by
    obtain ⟨d,hd,hdU⟩ := Metric.isOpen_iff.mp hU x hx
    let r := min η (min ε (d/2))
    have hr : 0 < r := lt_min hη (lt_min hε (half_pos hd))
    refine ⟨(x,r),⟨hr,min_le_left _ _,?_⟩,(min_le_right _ _).trans (min_le_left _ _),rfl⟩
    exact (closedBall_subset_ball (by
      have hh : r ≤ d/2 := (min_le_right _ _).trans (min_le_right _ _)
      linarith only [hh,hd])).trans hdU
  obtain ⟨J,hJT,hcount,hdisj,hcov⟩ := Vitali.exists_disjoint_covering_ae
    volume U T (3^n) (fun z => z.2) (fun z => z.1) (fun z => closedBall z.1 z.2)
    (fun _ _ => subset_rfl) hdouble
    (fun z hz => ⟨z.1,ball_subset_interior_closedBall (mem_ball_self hz.1)⟩)
    (fun _ _ => isClosed_closedBall) hf
  exact ⟨J,hcount,fun z hz => hJT hz,hdisj,hcov⟩

end RegularPointCoordinates

end

end OAI
