import OAI.Analysis.LipschitzHilbert.Phase.SourceSelectionAngularGeometry
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSelectedBoxSeparation

namespace OAI

noncomputable section
open Set
namespace LipschitzHilbert

namespace PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem angular_cell_distance (w : ℝ) (hw : 0<w) (grid : ℤ)
    (j : Fin N) (k : ℤ) (s t : ℝ)
    (hs : s∈scaledAngularCell (w/P.topLength) grid j.val k)
    (ht : t∈scaledAngularCell (w/P.topLength) grid j.val k) :
    |s-t|≤w/P.length j := by
  have h := scaledAngularCell_slope (div_pos hw P.topLength_pos)
    (le_refl (j.val:ℤ)) ⟨s,hs,hs⟩ hs ht
  have he : (w/P.topLength)*DyadicLineGrid.scale j.val=w/P.length j := by
    unfold length DyadicLineGrid.scale
    rw [zpow_natCast]
    field_simp [P.topLength_pos.ne']
  rwa [he] at h

namespace SizeStoppingRun
variable {P} {w cb tau sigma epsilon A : ℝ}
  {cell : ∀ j, P.labels j → ℤ} {grid : ℤ}
  {c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ}
  {initial remaining : Finset P.PacketIndex} {tops : List SlopeBox}

theorem selected_top_direction_bound
    (h : P.SizeStoppingRun false w cb tau sigma epsilon A cell grid c initial tops remaining)
    (hw : 0<w) (t : ℝ) (p : SlopeBox × Finset P.PacketIndex)
    (hp : p∈P.sizeSelectionRecords false w cb A cell grid initial tops)
    (q : P.PacketIndex) (hq : q∈p.2)
    (hrow : P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (hnear : |P.rowSlope q.1 q.2.1-t|≤cb*(w/P.length q.1)/4) :
    |p.1.slope-t|≤(1+cb/4)*(w/P.length q.1) := by
  have hgeom := (h.records_geometry p hp).2.2 q hq
  have hd := P.angular_cell_distance w hw grid q.1 (cell q.1 q.2.1)
    p.1.slope (P.rowSlope q.1 q.2.1) hgeom.2.2.1 hrow
  calc
    _ ≤ |p.1.slope-P.rowSlope q.1 q.2.1|+|P.rowSlope q.1 q.2.1-t| := abs_sub_le _ _ _
    _ ≤ w/P.length q.1+cb*(w/P.length q.1)/4 := add_le_add hd hnear
    _ = _ := by ring

/-- The geometric separation now needs only the packet-cell margins and
the two packet slope bounds; it does not assume the later top's direction. -/
theorem selected_boxes_disjoint_of_margin
    (h : P.SizeStoppingRun false w cb tau sigma epsilon A cell grid c initial tops remaining)
    (hw : 0<w) (hwW : w≤P.width) (hcb : 0<cb)
    (t K CZero : ℝ) (hK : 0≤K) (hCZero : 0<CZero)
    (hconstants : (1+cb/4)/CZero≤cb/4)
    (hA : 2*K*(1+(1+cb/4))+1/2≤A)
    (p p' : SlopeBox × Finset P.PacketIndex)
    (hp : p∈P.sizeSelectionRecords false w cb A cell grid initial tops)
    (hp' : p'∈P.sizeSelectionRecords false w cb A cell grid initial tops)
    (q q' : P.PacketIndex) (hq : q∈p.2) (hq' : q'∈p'.2)
    (hlen : P.length q.1≤P.length q'.1)
    (hfar : CZero*P.length q.1≤P.length q'.1)
    (hnear : |P.rowSlope q.1 q.2.1-t|≤cb*(w/P.length q.1)/4)
    (hnear' : |P.rowSlope q'.1 q'.2.1-t|≤cb*(w/P.length q'.1)/4)
    (hrow' : P.rowSlope q'.1 q'.2.1∈scaledAngularCell (w/P.topLength) grid q'.1.val (cell q'.1 q'.2.1))
    (hepsilon : epsilon≤cb*(w/P.length q.1)/4)
    (hmargin : Icc (P.rowSlope q.1 q.2.1-cb*(w/P.length q.1)/2)
      (P.rowSlope q.1 q.2.1+cb*(w/P.length q.1)/2)⊆
        scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) :
    Disjoint (densitySpatialBox (P.directionBox t q) K)
      (densitySpatialBox (P.directionBox t q') K) := by
  have ht := h.selected_top_direction_bound hw t p' hp' q' hq' hrow' hnear'
  have hpos : 0≤1+cb/4 := by linarith
  have hs := angular_scale_ratio w (P.length q.1) (P.length q'.1) CZero hw.le
    (P.length_pos q.1) (P.length_pos q'.1) hCZero hfar
  have htnear : |p'.1.slope-t|≤cb*(w/P.length q.1)/4 := by
    calc
      _ ≤ (1+cb/4)*((1/CZero)*(w/P.length q.1)) :=
        ht.trans (mul_le_mul_of_nonneg_left hs hpos)
      _ = ((1+cb/4)/CZero)*(w/P.length q.1) := by ring
      _ ≤ (cb/4)*(w/P.length q.1) :=
        mul_le_mul_of_nonneg_right hconstants (div_nonneg hw.le (P.length_pos q.1).le)
      _ = _ := by ring
  have htscaled : |p'.1.slope-t| * P.length q'.1≤(1+cb/4)*P.width := by
    calc
      _ ≤ ((1+cb/4)*(w/P.length q'.1))*P.length q'.1 :=
        mul_le_mul_of_nonneg_right ht (P.length_pos q'.1).le
      _ = (1+cb/4)*w := by field_simp [(P.length_pos q'.1).ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hwW hpos
  have htcell : p'.1.slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1) := by
    apply hmargin
    have hd : |p'.1.slope-P.rowSlope q.1 q.2.1|≤cb*(w/P.length q.1)/2 := by
      calc
        _ ≤ |p'.1.slope-t|+|t-P.rowSlope q.1 q.2.1| := abs_sub_le _ _ _
        _ ≤ cb*(w/P.length q.1)/4+cb*(w/P.length q.1)/4 :=
          add_le_add htnear (by simpa only [abs_sub_comm] using hnear)
        _ = _ := by ring
    obtain ⟨hl,hr⟩ := abs_le.mp hd
    constructor <;> linarith
  exact h.selected_boxes_disjoint hw hcb t K (1+cb/4) hK hpos hA p p' hp hp' q q' hq hq'
    hlen hnear htnear htscaled hepsilon htcell

end SizeStoppingRun
end PacketLatticeData
end LipschitzHilbert

end

end OAI
