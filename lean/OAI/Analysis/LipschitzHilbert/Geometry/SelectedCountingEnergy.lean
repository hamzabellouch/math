import OAI.Analysis.LipschitzHilbert.Geometry.NearPairEnergy
import OAI.Analysis.LipschitzHilbert.Geometry.FarPairEnergy

namespace OAI

/-! The actual selected rectangle count has the Lacey--Li second moment
bound. Both near and far overlaps have been proved from non-removal. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators Classical
namespace LipschitzHilbert

theorem selected_counting_energy {ι : Type*} [DecidableEq ι] {n : ℕ}
    (D : Fin n → Rectangle)
    (hD : ∀ T : Rectangle, ∃ i, dist ((D i).axes 0) (T.axes 1) < 1/4)
    (R : ι → Rectangle) (stock : Finset ι) (selected : List ι)
    (hrun : RectangleCoverRun R
      (maximalBlocked (fun i => (D i).orthogonalCoordinates) R
        selectionDilation (by norm_num) selectionThreshold) ∅ stock selected)
    {v : Plane → Plane} {K δ : ℝ≥0} (hv : LipschitzWith K v) (hu : ∀ x, ‖v x‖ = 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hR : ∀ j ∈ stock, (R j).Admissible v K δ) :
    (δ : ℝ≥0∞)*(∫⁻ x, (rectangleCount R selected.toFinset x)^2) ≤
      1923*(∑ j ∈ selected.toFinset, volume (R j).carrier) := by
  let A := ∑ j ∈ selected.toFinset, volume (R j).carrier
  have hn := selected_near_energy D hD R hrun (by simp) (by simp)
  have hn' : orderedPairSum (nearPair R) selected ≤ A := by
    simpa only [previousPairSum,Finset.sum_empty,Finset.sum_const_zero,zero_add] using hn
  have hf := selected_far_energy D hD R hrun hv hu hδ hR
  have hd : (δ : ℝ≥0∞) ≤ 1 := by exact_mod_cast hδ1.le
  have hdn : (δ : ℝ≥0∞)*orderedPairSum (nearPair R) selected ≤ A := by
    calc
      _ ≤ 1*A := mul_le_mul' hd hn'
      _ = A := one_mul _
  have hda : (δ : ℝ≥0∞)*A ≤ A := by simpa only [one_mul] using mul_le_mul' hd (le_refl A)
  have hsplit : orderedPairSum (overlapPair R) selected =
      orderedPairSum (nearPair R) selected+orderedPairSum (farPair R) selected := by
    have he : overlapPair R = fun i j => nearPair R i j+farPair R i j := by
      funext i j
      exact overlapPair_split R i j
    rw [he,orderedPairSum_split]
  rw [rectangleCount_second_moment]
  change (δ : ℝ≥0∞)*(∑ i ∈ selected.toFinset, ∑ j ∈ selected.toFinset, overlapPair R i j) ≤ 1923*A
  rw [list_overlap_energy R selected hrun.selected_nodup,hsplit]
  calc
    _ = (δ : ℝ≥0∞)*A+2*((δ : ℝ≥0∞)*orderedPairSum (nearPair R) selected)+
        2*((δ : ℝ≥0∞)*orderedPairSum (farPair R) selected) := by ring
    _ ≤ A+2*A+2*(960*A) := add_le_add (add_le_add hda (mul_le_mul' le_rfl hdn))
      (mul_le_mul' le_rfl hf)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
