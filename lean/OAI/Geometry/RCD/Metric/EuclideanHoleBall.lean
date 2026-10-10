import OAI.Geometry.RCD.Metric.RescalingVolumeDensity
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

/-! # A ball inside an open Euclidean hole with an interior boundary contact

The elementary enlargement step in De Philippis--Gigli (2018), Lemma 3.3,
used for the image-volume estimate in Proposition 3.2.
-/

open Set Metric
noncomputable section
namespace RegularPointCoordinates

theorem euclidean_hole_ball {n : ℕ} {A : Set (Euclidean n)} (hA : IsOpen A)
    (hproper : ∃ q ∈ ball (0 : Euclidean n) 1, q ∉ A)
    {y : Euclidean n} {r : ℝ} (hr : 0 < r) (hroom : ‖y‖+r < 1)
    (hin : closedBall y r ⊆ A) :
    ∃ (c : Euclidean n) (R : ℝ), 0 < R ∧ R < 1 ∧ ball y r ⊆ ball c R ∧ ball c R ⊆ A ∧
      closedBall c R ⊆ ball 0 1 ∧ (sphere c R ∩ frontier A).Nonempty := by
  obtain ⟨q,hq,hqA⟩ := hproper
  have hAc : Aᶜ.Nonempty := ⟨q,hqA⟩
  let c := fun t : ℝ => (1-t) • y
  let R := fun t : ℝ => (1-t)*r+t
  let d := fun t : ℝ => infDist (c t) Aᶜ - R t
  have hd : Continuous d := (continuous_infDist_pt Aᶜ |>.comp
    ((continuous_const.sub continuous_id).smul continuous_const)).sub
      ((continuous_const.sub continuous_id).mul continuous_const |>.add continuous_id)
  have hd0 : 0 < d 0 := by
    obtain ⟨z,hz,hzdist⟩ := hA.isClosed_compl.exists_infDist_eq_dist hAc y
    have hzr : r < dist y z := by
      by_contra h
      have hzball : z ∈ closedBall y r := by rw [mem_closedBall,dist_comm]; exact le_of_not_gt h
      exact hz (hin hzball)
    simpa only [d,c,R,sub_zero,one_smul,one_mul,add_zero,hzdist] using sub_pos.mpr hzr
  have hd1 : d 1 < 0 := by
    have hi := infDist_le_dist_of_mem (x := (0 : Euclidean n)) (s := Aᶜ) hqA
    have hqn : dist (0 : Euclidean n) q < 1 := by
      simpa only [mem_ball,dist_zero_left,dist_zero_right] using hq
    simpa only [d,c,R,sub_self,zero_smul,zero_mul,zero_add] using sub_neg.mpr (hi.trans_lt hqn)
  obtain ⟨t,ht,hdt⟩ := intermediate_value_Icc' (show (0:ℝ) ≤ 1 by norm_num) hd.continuousOn
    (show (0:ℝ) ∈ Icc (d 1) (d 0) from ⟨hd1.le,hd0.le⟩)
  have ht0 : 0 < t := lt_of_le_of_ne ht.1 (by intro h; subst t; exact hd0.ne' hdt)
  have ht1 : t < 1 := lt_of_le_of_ne ht.2 (by intro h; subst t; exact hd1.ne hdt)
  have hdist : infDist (c t) Aᶜ=R t := sub_eq_zero.mp hdt
  have hR : 0 < R t := add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2) hr.le) ht0
  have hc : ‖c t‖=(1-t)*‖y‖ := by
    change ‖(1-t) • y‖=(1-t)*‖y‖
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr ht.2)]
  have hnorm : ‖c t‖+R t < 1 := by
    rw [hc]
    dsimp only [R]
    nlinarith [mul_pos (sub_pos.mpr ht1) (sub_pos.mpr hroom)]
  have hinside : ball (c t) (R t) ⊆ A := by
    rw [← hdist]
    exact ball_infDist_compl_subset
  refine ⟨c t,R t,hR,by linarith [norm_nonneg (c t)],?_,hinside,?_,?_⟩
  · intro x hx
    have hcy : dist y (c t)=t*‖y‖ := by
      rw [dist_eq_norm]
      have he : y-(1-t) • y=t • y := by module
      change ‖y-(1-t) • y‖=t*‖y‖
      rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
    have htriangle := dist_triangle x y (c t)
    rw [hcy] at htriangle
    have hxr : dist x y < r := hx
    change dist x (c t) < (1-t)*r+t
    nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hroom.le)]
  · intro x hx
    have htriangle := norm_le_norm_add_norm_sub (c t) x
    rw [norm_sub_rev (c t) x] at htriangle
    have hxr : ‖x-c t‖ ≤ R t := by simpa only [mem_closedBall,dist_eq_norm] using hx
    change ‖x-0‖ < 1
    rw [sub_zero]
    linarith
  · obtain ⟨z,hz,hzdist⟩ := hA.isClosed_compl.exists_infDist_eq_dist hAc (c t)
    have hzs : z ∈ sphere (c t) (R t) := by
      rw [mem_sphere,dist_comm,← hzdist,hdist]
    refine ⟨z,hzs,?_⟩
    rw [hA.frontier_eq]
    refine ⟨?_,hz⟩
    apply closure_mono hinside
    rw [closure_ball (c t) (ne_of_gt hR)]
    exact sphere_subset_closedBall hzs

end RegularPointCoordinates

end

end OAI
