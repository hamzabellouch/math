import OAI.Analysis.LipschitzHilbert.Geometry.FarSlabLineSum

namespace OAI

/-! The long-rectangle exclusion estimate (Lacey--Li, Lemma 3.16) from
actual non-removal. The finite direction net is the one already used
in the near-angle selection estimate. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert

private theorem long_slab_threshold : ENNReal.ofReal 6144*selectionThreshold < 1 := by
  change ENNReal.ofReal 6144*ENNReal.ofReal (1/1048576:ℝ) < 1
  rw [←ENNReal.ofReal_mul (by norm_num),ENNReal.ofReal_lt_one]
  norm_num

theorem far_slab_selected_bound {ι : Type*} {n : ℕ}
    (D : Fin n → Rectangle)
    (hD : ∀ T : Rectangle, ∃ i, dist ((D i).axes 0) (T.axes 1) < 1/4)
    (R : ι → Rectangle) (s previous : Finset ι) (r : ι) (hs : s ⊆ previous)
    (S : Rectangle) (c l θ : ℝ)
    (hl : 0 < l) (hθ : 0 < θ) (hθsmall : θ ≤ 1/20)
    (hRlong : ∀ j ∈ s, 8*l ≤ (R j).long) (hTlong : (R r).long ≤ l)
    (hSshort : S.short ≤ θ*l) (hTshort : (R r).short ≤ θ*l)
    (hRangle : ∀ j ∈ s, dist (S.axes 0) ((R j).axes 0) ≤ 2*θ)
    (hRlower : ∀ j ∈ s, θ/2 ≤ dist (S.axes 0) ((R j).axes 0))
    (hTangle : dist (S.axes 0) ((R r).axes 0) ≤ 2*θ)
    (hR : ∀ j ∈ s, ((R j).carrier ∩ S.stripSlab c l).Nonempty)
    (hT : ((R r).carrier ∩ S.stripSlab c (4*l)).Nonempty)
    (hnot : ¬maximalBlocked (fun i => (D i).orthogonalCoordinates) R
      selectionDilation (by norm_num) selectionThreshold previous r) :
    (∑ j ∈ s, volume ((R j).carrier ∩ S.stripSlab c l)) < volume (S.stripSlab c l) := by
  classical
  obtain ⟨i,hi⟩ := hD S
  have htrans (j : ι) (hj : j ∈ s) : 1/2 ≤ |(R j).axes.repr ((D i).axes 0) 1| := by
    exact Rectangle.nearby_transverse_coordinate S (R j) (D i)
      (by rw [dist_comm]; linarith [hRangle j hj]) hi.le
  let e := fun i => (D i).orthogonalCoordinates
  let g := rectangleCount (fun j => (R j).dilate 265 (by norm_num)) previous
  have hpoint : ∃ x ∈ (R r).carrier, positiveAuxiliary e g x ≤ selectionThreshold := by
    by_contra hn
    push Not at hn
    exact hnot hn
  obtain ⟨x,hx,hvalue⟩ := hpoint
  have hline := far_slab_line_sum D R s S (R r) i c l θ hl hθ hθsmall hRlong hTlong
    hSshort hTshort hRangle hRlower hTangle hR hT htrans x hx
  have hm := positiveAuxiliary_mono e
    (rectangleCount_mono (fun j => (R j).dilate 265 (by norm_num)) hs) x
  have hpos : volume (S.stripSlab c l) ≠ 0 := by
    rw [S.volume_stripSlab]
    exact mul_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr hl))
      (ne_of_gt (ENNReal.ofReal_pos.mpr S.short_pos))
  have htop : volume (S.stripSlab c l) ≠ ∞ := by
    rw [S.volume_stripSlab]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  calc
    _ ≤ ENNReal.ofReal 6144*volume (S.stripSlab c l)*
        positiveAuxiliary e (rectangleCount (fun j => (R j).dilate 265 (by norm_num)) s) x := hline
    _ ≤ ENNReal.ofReal 6144*volume (S.stripSlab c l)*selectionThreshold :=
      mul_le_mul' le_rfl (hm.trans hvalue)
    _ = (ENNReal.ofReal 6144*selectionThreshold)*volume (S.stripSlab c l) := by ring
    _ < 1*volume (S.stripSlab c l) :=
      (ENNReal.mul_lt_mul_iff_left hpos htop).mpr long_slab_threshold
    _ = _ := one_mul _

private theorem comparable_slab_threshold : ENNReal.ofReal 49152*selectionThreshold < 1 := by
  change ENNReal.ofReal 49152*ENNReal.ofReal (1/1048576:ℝ) < 1
  rw [←ENNReal.ofReal_mul (by norm_num),ENNReal.ofReal_lt_one]
  norm_num

theorem comparable_slab_selected_bound {ι : Type*} {n : ℕ}
    (D : Fin n → Rectangle)
    (hD : ∀ T : Rectangle, ∃ i, dist ((D i).axes 0) (T.axes 1) < 1/4)
    (R : ι → Rectangle) (s previous : Finset ι) (r : ι) (hs : s ⊆ previous)
    (S : Rectangle) (c l θ : ℝ)
    (hl : 0 < l) (hθ : 0 < θ) (hθsmall : θ ≤ 1/20)
    (hRlong : ∀ j ∈ s, l ≤ (R j).long) (hTlong : (R r).long ≤ 16*l)
    (hSshort : S.short ≤ θ*l) (hTshort : (R r).short ≤ θ*l)
    (hRangle : ∀ j ∈ s, dist (S.axes 0) ((R j).axes 0) ≤ 2*θ)
    (hRlower : ∀ j ∈ s, θ/2 ≤ dist (S.axes 0) ((R j).axes 0))
    (hTangle : dist (S.axes 0) ((R r).axes 0) ≤ 2*θ)
    (hR : ∀ j ∈ s, ((R j).carrier ∩ S.stripSlab c l).Nonempty)
    (hT : ((R r).carrier ∩ S.stripSlab c (4*l)).Nonempty)
    (hnot : ¬maximalBlocked (fun i => (D i).orthogonalCoordinates) R
      selectionDilation (by norm_num) selectionThreshold previous r) :
    (∑ j ∈ s, volume ((R j).carrier ∩ S.stripSlab c l)) < volume (S.stripSlab c l) := by
  classical
  obtain ⟨i,hi⟩ := hD S
  have htrans (j : ι) (hj : j ∈ s) : 1/2 ≤ |(R j).axes.repr ((D i).axes 0) 1| := by
    exact Rectangle.nearby_transverse_coordinate S (R j) (D i)
      (by rw [dist_comm]; linarith [hRangle j hj]) hi.le
  let e := fun i => (D i).orthogonalCoordinates
  let g := rectangleCount (fun j => (R j).dilate 265 (by norm_num)) previous
  have hpoint : ∃ x ∈ (R r).carrier, positiveAuxiliary e g x ≤ selectionThreshold := by
    by_contra hn
    push Not at hn
    exact hnot hn
  obtain ⟨x,hx,hvalue⟩ := hpoint
  have hline := comparable_slab_line_sum D R s S (R r) i c l θ hl hθ hθsmall hRlong hTlong
    hSshort hTshort hRangle hRlower hTangle hR hT htrans x hx
  have hm := positiveAuxiliary_mono e
    (rectangleCount_mono (fun j => (R j).dilate 265 (by norm_num)) hs) x
  have hpos : volume (S.stripSlab c l) ≠ 0 := by
    rw [S.volume_stripSlab]
    exact mul_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr hl))
      (ne_of_gt (ENNReal.ofReal_pos.mpr S.short_pos))
  have htop : volume (S.stripSlab c l) ≠ ∞ := by
    rw [S.volume_stripSlab]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  calc
    _ ≤ ENNReal.ofReal 49152*volume (S.stripSlab c l)*
        positiveAuxiliary e (rectangleCount (fun j => (R j).dilate 265 (by norm_num)) s) x := hline
    _ ≤ ENNReal.ofReal 49152*volume (S.stripSlab c l)*selectionThreshold :=
      mul_le_mul' le_rfl (hm.trans hvalue)
    _ = (ENNReal.ofReal 49152*selectionThreshold)*volume (S.stripSlab c l) := by ring
    _ < 1*volume (S.stripSlab c l) :=
      (ENNReal.mul_lt_mul_iff_left hpos htop).mpr comparable_slab_threshold
    _ = _ := one_mul _

end LipschitzHilbert

end

end OAI
