import OAI.Analysis.LipschitzHilbert.Geometry.FiniteTransverseDirections
import OAI.Analysis.LipschitzHilbert.Geometry.FatRectangleSum

namespace OAI

/-! A universal near-angle selected overlap bound, with all directional
and aspect-ratio choices discharged. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert

abbrev selectionDilation : ℝ := 265
abbrev selectionThreshold : ℝ≥0∞ := ENNReal.ofReal (1/1048576 : ℝ)

private theorem selectionThreshold_mul_le (c : ℝ) (hc : 0 ≤ c) (hcle : c ≤ 1048576) :
    ENNReal.ofReal c * selectionThreshold ≤ 1 := by
  change ENNReal.ofReal c * ENNReal.ofReal (1/1048576 : ℝ) ≤ 1
  rw [←ENNReal.ofReal_one,←ENNReal.ofReal_mul hc]
  apply ENNReal.ofReal_le_ofReal
  have h : c/(1048576:ℝ) ≤ 1 := (div_le_iff₀ (by norm_num)).mpr (by simpa using hcle)
  simpa only [div_eq_mul_inv,one_div,one_mul] using h

theorem uniform_near_selected_overlap {ι : Type*} {n : ℕ} (D : Fin n → Rectangle)
    (hD : ∀ T : Rectangle, ∃ i, dist ((D i).axes 0) (T.axes 1) < 1/4)
    (R : ι → Rectangle) (s previous : Finset ι) (hs : s ⊆ previous) (r : ι)
    (hL : ∀ j ∈ s, (R r).long ≤ (R j).long)
    (hnear : ∀ j ∈ s, (R r).long * dist ((R j).axes 0) ((R r).axes 0) ≤ 64*(R r).short)
    (hnot : ¬maximalBlocked (fun i => (D i).orthogonalCoordinates) R
      selectionDilation (by norm_num) selectionThreshold previous r) :
    (∑ j ∈ s, volume ((R r).carrier ∩ (R j).carrier)) ≤ volume (R r).carrier := by
  by_cases hfat : (R r).long ≤ 256*(R r).short
  · exact fat_selected_overlap_bound (fun i => (D i).orthogonalCoordinates) R s previous hs r
      256 (by norm_num) hfat selectionDilation (by norm_num) selectionThreshold (selectionThreshold_mul_le _ (by norm_num) (by norm_num)) hnot
  · obtain ⟨i,hi⟩ := hD (R r)
    have htrans (j : ι) (hj : j ∈ s) : 1/2 ≤ |(R j).axes.repr ((D i).axes 0) 1| := by
      apply Rectangle.nearby_transverse_coordinate (R r) (R j) (D i) _ hi.le
      have hh := hnear j hj
      have hp := (R r).long_pos
      have hn : 256*(R r).short < (R r).long := lt_of_not_ge hfat
      nlinarith
    have hsmall : ENNReal.ofReal (96*((64:ℝ)+1))*selectionThreshold ≤ 1 := by
      exact selectionThreshold_mul_le _ (by norm_num) (by norm_num)
    have haeq : 4*((64:ℝ)+1)+5 = selectionDilation := by norm_num [selectionDilation]
    have hn : ¬maximalBlocked (fun i => (D i).orthogonalCoordinates) R
        (4*((64:ℝ)+1)+5) (by norm_num) selectionThreshold previous r := by
      simpa only [haeq] using hnot
    exact near_selected_overlap_bound D R s previous r i 64 (by norm_num) hs
      selectionThreshold hsmall hL hnear htrans hn

end LipschitzHilbert

end

end OAI
