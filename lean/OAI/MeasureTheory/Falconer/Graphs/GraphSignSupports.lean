import OAI.MeasureTheory.Falconer.Graphs.GraphChartVariation
import OAI.MeasureTheory.Falconer.Graphs.GraphSignPartition
import OAI.MeasureTheory.Falconer.Angular.RotatedConeKernel

namespace OAI

namespace PlanarFalconer
open Set

theorem sourceConeCircle_tsupport_dist (axis : ℝ) :
    tsupport (sourceConeCircle axis) ⊆ {dir | dist dir (sourceUnitDirection axis) ≤ 2/5} := by
  apply closure_minimal
  · intro dir hdir
    have ht := graphConeCutoff_support (subset_closure hdir)
    change sourceAngle (sourceCircleRotate (-axis) dir) ∈ Icc (-1/5:ℝ) (1/5) at ht
    have hd := sourceDirection_dist_le (sourceAngle (sourceCircleRotate (-axis) dir)) 0
    have hb : dist (sourceCircleRotate (-axis) dir) (sourceUnitDirection 0) ≤ 2/5 := by
      rw [← sourceUnitDirection_sourceAngle (sourceCircleRotate (-axis) dir)]
      change dist (sourceDirection _) (sourceDirection 0) ≤ _
      rw [Real.dist_eq, sub_zero] at hd
      have ha : |sourceAngle (sourceCircleRotate (-axis) dir)| ≤ 1/5 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      linarith
    have he := sourceCircleRotate_dist axis (sourceCircleRotate (-axis) dir) (sourceUnitDirection 0)
    simp only [sourceCircleRotate_add, neg_add_cancel, sourceCircleRotate_zero,
      sourceCircleRotate_comp, zero_add] at he
    change dist dir (sourceUnitDirection axis) ≤ 2/5
    rwa [he]
  · exact isClosed_le (by fun_prop) continuous_const

theorem sourceConeCircle_plus_nondegenerate (axis : ℝ) (u v : UnitCircle)
    (hu : u ∈ tsupport (sourceConeCircle axis)) (hv : v ∈ tsupport (sourceConeCircle axis)) :
    6/5 ≤ ‖(u:Plane)+(v:Plane)‖ := by
  have hu' := sourceConeCircle_tsupport_dist axis hu
  have hv' := sourceConeCircle_tsupport_dist axis hv
  let a : Plane := sourceDirection axis
  have ha : ‖a+a‖ = 2 := by
    rw [← two_smul ℝ a, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ)<2)]
    simp [a, norm_sourceDirection]
  have hd := dist_add_add_le a a (u:Plane) (v:Plane)
  have hn := norm_sub_norm_le (a+a) ((u:Plane)+(v:Plane))
  rw [ha] at hn
  rw [dist_eq_norm] at hd
  change dist (u:Plane) a ≤ 2/5 at hu'
  change dist (v:Plane) a ≤ 2/5 at hv'
  rw [dist_comm (u:Plane) a] at hu'
  rw [dist_comm (v:Plane) a] at hv'
  linarith

noncomputable def circleGraphSignWeight (s : ℝ) : UnitCircle × UnitCircle → ℝ :=
  if s = 1 then circleGraphSignPlus else circleGraphSignMinus

theorem circleGraphSignWeight_nondegenerate (s : ℝ) (hs : s = 1 ∨ s = -1)
    {p : UnitCircle × UnitCircle} (hp : p ∈ tsupport (circleGraphSignWeight s)) :
    1/2 ≤ ‖(p.1:Plane)+s • (p.2:Plane)‖ := by
  rcases hs with rfl | rfl
  · simp only [circleGraphSignWeight] at hp
    simpa only [one_smul] using (show (1/2:ℝ) ≤ 1 by norm_num).trans
      (circleGraphSignPlus_tsupport hp)
  · norm_num [circleGraphSignWeight] at hp
    have hh := circleGraphSignMinus_tsupport hp
    simpa only [neg_one_smul, ← sub_eq_add_neg] using
      (show (1/2:ℝ) ≤ 1 by norm_num).trans hh

def graphBinPairSupport (δ s : ℝ) (j k : ℕ) : Set (UnitCircle × UnitCircle) :=
  ((tsupport (circleAngularBin (angularBinCount δ) j)) ×ˢ
    (tsupport (circleAngularBin (angularBinCount δ) k))) ∩ tsupport (circleGraphSignWeight s)

theorem actual_graph_bin_pair_representative {δ : ℝ} (hδ : 0 < δ) (hcap : δ ≤ 2*Real.pi)
    (s : ℝ) (hs : s = 1 ∨ s = -1) (j k : ℕ) (hS : (graphBinPairSupport δ s j k).Nonempty) :
    ∃ q ∈ graphBinPairSupport δ s j k, ∀ p ∈ graphBinPairSupport δ s j k,
      |graphChartZ (p.1:Plane) (s • (p.2:Plane))-graphChartZ (q.1:Plane) (s • (q.2:Plane))|+
      dist (graphChartAxis (p.1:Plane) (s • (p.2:Plane)))
        (graphChartAxis (q.1:Plane) (s • (q.2:Plane))) ≤ 112*δ := by
  have he := graph_complete_support_representative s (4*δ) hs _ hS
    (fun p hp => circleGraphSignWeight_nondegenerate s hs hp.2)
    (fun p hp q hq => ⟨circleAngularBin_scale_diameter hδ hcap j hp.1.1 hq.1.1,
      circleAngularBin_scale_diameter hδ hcap k hp.1.2 hq.1.2⟩)
  rw [show 28*(4*δ) = 112*δ by ring] at he
  exact he

end PlanarFalconer

end OAI
