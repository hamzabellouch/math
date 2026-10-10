import OAI.Analysis.CircleDomains.Topology.ThickenedContinuumDisk
import OAI.Analysis.CircleDomains.Topology.SimpleArcsProof
import OAI.Analysis.CircleDomains.Topology.CrosscutSeparationInput
import Mathlib.Analysis.Convex.PathConnected

namespace OAI

/-! A connected compact set in the closed disk can be replaced by a simple
crosscut with the same two boundary endpoints while avoiding a disjoint closed set. -/
open Set Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma radial_segment_in_thickened_disk {A : Set ℂ} {a : ℂ} (ha : a ∈ A)
    (han : ‖a‖ = 1) {r δ : ℝ} (hr : 0 < r) (hr1 : r < 1) (hrδ : 1-r < δ) :
    range (Path.segment a (r • a)) ⊆ insert a (thickening δ A ∩ ball (0 : ℂ) 1) := by
  rintro z ⟨t,rfl⟩
  by_cases ht0 : t = 0
  · exact Or.inl (by rw [ht0,(Path.segment a (r • a)).source])
  have ht : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1
    (fun h => ht0 (Subtype.ext h.symm))
  let s : ℝ := 1-(t : ℝ)+(t : ℝ)*r
  have hsr : r ≤ s := by dsimp [s]; nlinarith [t.property.2]
  have hs : 0 < s := hr.trans_le hsr
  have hs1 : s < 1 := by dsimp [s]; nlinarith
  have he : Path.segment a (r • a) t = s • a := by
    simp only [Path.segment_apply,AffineMap.lineMap_apply_module,smul_smul,← add_smul]
    rfl
  rw [he]
  right
  refine ⟨mem_thickening_iff.mpr ⟨a,ha,?_⟩,?_⟩
  · exact (inner_disk_scale_dist hs hs1 han.le).trans_lt (by linarith)
  · rw [mem_ball_zero_iff,norm_smul,Real.norm_eq_abs,abs_of_pos hs,han,mul_one]
    exact hs1

lemma exists_disk_crosscut_avoiding {A B : Set ℂ}
    (hAc : IsCompact A) (hA : IsConnected A) (hAd : A ⊆ closedBall (0 : ℂ) 1)
    (hBc : IsClosed B) (hAB : Disjoint A B)
    {a b : ℂ} (ha : a ∈ A) (hb : b ∈ A) (han : ‖a‖ = 1) (hbn : ‖b‖ = 1)
    (hab : a ≠ b) :
    ∃ p : Path a b, Injective p ∧
      (∀ t ∈ Ioo (0 : PathTime) 1, ‖p t‖ < 1) ∧ Disjoint (range p) B := by
  obtain ⟨δ,hδ,hδB⟩ := hAc.exists_thickening_subset_open hBc.isOpen_compl
    (Set.disjoint_left.mp hAB)
  obtain ⟨r,hr,hr1,hrδ⟩ := exists_inner_disk_scale hδ
  let U := thickening δ A ∩ ball (0 : ℂ) 1
  have hU : IsOpen U := isOpen_thickening.inter isOpen_ball
  have hUc : IsConnected U := isConnected_thickening_inter_disk hA hAd hδ
  have hmem (x : ℂ) (hx : x ∈ A) : r • x ∈ U := by
    have hxn := mem_closedBall_zero_iff.mp (hAd hx)
    refine ⟨mem_thickening_iff.mpr ⟨x,hx,(inner_disk_scale_dist hr hr1 hxn).trans_lt hrδ⟩,?_⟩
    rw [mem_ball_zero_iff,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    exact (mul_le_of_le_one_right hr.le hxn).trans_lt hr1
  obtain ⟨η,hη⟩ := (hU.isConnected_iff_isPathConnected.mp hUc).joinedIn _ (hmem a ha) _ (hmem b hb)
  let γ := ((Path.segment a (r • a)).trans η).trans (Path.segment b (r • b)).symm
  have hγ : range γ ⊆ insert a (insert b U) := by
    rw [Path.trans_range,Path.trans_range,Path.symm_range]
    apply union_subset
    · apply union_subset
      · exact (radial_segment_in_thickened_disk ha han hr hr1 hrδ).trans
          (insert_subset_insert (subset_insert b U))
      · exact (range_subset_iff.mpr hη).trans ((subset_insert b U).trans (subset_insert a _))
    · intro z hz
      rcases radial_segment_in_thickened_disk hb hbn hr hr1 hrδ hz with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  obtain ⟨p,hpi,hpγ⟩ := exists_injective_subpath γ hab
  have hp := hpγ.trans hγ
  refine ⟨p,hpi,?_,?_⟩
  · intro t ht
    rcases hp (mem_range_self t) with he | he | hu
    · have he' : p t = p 0 := he.trans p.source.symm
      exact (ne_of_gt ht.1 (hpi he')).elim
    · have he' : p t = p 1 := he.trans p.target.symm
      exact (ne_of_lt ht.2 (hpi he')).elim
    · exact mem_ball_zero_iff.mp hu.2
  · apply Set.disjoint_left.mpr
    intro z hz hzB
    rcases hp hz with rfl | rfl | hu
    · exact Set.disjoint_left.mp hAB ha hzB
    · exact Set.disjoint_left.mp hAB hb hzB
    · exact hδB hu.1 hzB

end CircleDomainRigidity

end

end OAI
