import OAI.Analysis.CircleDomains.Topology.ConnectedDiskIntersection
import Mathlib.Topology.MetricSpace.Thickening

namespace OAI

/-! A small open neighborhood of a connected subset of the closed disk
remains connected when restricted to the open disk. -/
open Set Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exists_inner_disk_scale {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ 1-r < δ := by
  obtain ⟨r,hr,hr1⟩ := exists_between (max_lt (by norm_num : (0 : ℝ) < 1)
    (by linarith : 1-δ < 1))
  exact ⟨r,(le_max_left _ _).trans_lt hr,hr1,by linarith [le_max_right (0 : ℝ) (1-δ)]⟩

lemma inner_disk_scale_dist {r : ℝ} (_hr : 0 < r) (hr1 : r < 1)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : dist (r • z) z ≤ 1-r := by
  calc
    dist (r • z) z = ‖(r-1) • z‖ := by rw [dist_eq_norm,sub_smul,one_smul]
    _ = (1-r) * ‖z‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_neg (sub_neg.mpr hr1)]; ring
    _ ≤ (1-r)*1 := mul_le_mul_of_nonneg_left hz (by linarith)
    _ = 1-r := mul_one _

lemma isConnected_thickening_inter_disk {A : Set ℂ} (hA : IsConnected A)
    (hAd : A ⊆ closedBall (0 : ℂ) 1) {δ : ℝ} (hδ : 0 < δ) :
    IsConnected (thickening δ A ∩ ball (0 : ℂ) 1) := by
  obtain ⟨r,hr,hr1,hrδ⟩ := exists_inner_disk_scale hδ
  let C := (fun z : ℂ => r • z) '' A
  have hC : IsConnected C := hA.image _ (continuous_const_smul (T := ℂ) r).continuousOn
  have hscaled (a : ℂ) (ha : a ∈ A) :
      r • a ∈ ball a δ ∩ ball (0 : ℂ) 1 := by
    have han : ‖a‖ ≤ 1 := mem_closedBall_zero_iff.mp (hAd ha)
    refine ⟨(inner_disk_scale_dist hr hr1 han).trans_lt hrδ,?_⟩
    rw [mem_ball_zero_iff,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    exact (mul_le_of_le_one_right hr.le han).trans_lt hr1
  have hCU : C ⊆ thickening δ A ∩ ball (0 : ℂ) 1 := by
    rintro z ⟨a,ha,rfl⟩
    exact ⟨mem_thickening_iff.mpr ⟨a,ha,(hscaled a ha).1⟩,(hscaled a ha).2⟩
  have hp : IsPreconnected (⋃ a : A, C ∪ (ball (a : ℂ) δ ∩ ball 0 1)) := by
    obtain ⟨c,hc⟩ := hC.nonempty
    apply isPreconnected_iUnion
    · exact ⟨c,mem_iInter.mpr (fun _ => Or.inl hc)⟩
    · intro a
      exact hC.isPreconnected.union (r • (a : ℂ)) ⟨a,a.property,rfl⟩ (hscaled a a.property)
        ((convex_ball (a : ℂ) δ).inter (convex_ball 0 1)).isPreconnected
  have he : (⋃ a : A, C ∪ (ball (a : ℂ) δ ∩ ball 0 1)) =
      thickening δ A ∩ ball (0 : ℂ) 1 := by
    ext z
    constructor
    · intro hz
      obtain ⟨a,ha⟩ := mem_iUnion.mp hz
      rcases ha with h | h
      · exact hCU h
      · exact ⟨mem_thickening_iff.mpr ⟨a,a.property,h.1⟩,h.2⟩
    · rintro ⟨hz,hzb⟩
      obtain ⟨a,ha,hza⟩ := mem_thickening_iff.mp hz
      exact mem_iUnion.mpr ⟨⟨a,ha⟩,Or.inr ⟨hza,hzb⟩⟩
  obtain ⟨c,hc⟩ := hC.nonempty
  exact ⟨⟨c,hCU hc⟩,he ▸ hp⟩

end CircleDomainRigidity

end

end OAI
