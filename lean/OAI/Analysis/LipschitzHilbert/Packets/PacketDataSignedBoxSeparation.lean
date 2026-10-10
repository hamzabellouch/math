import OAI.Analysis.LipschitzHilbert.Phase.PacketDataSelectionAngularGeometry

namespace OAI

/-! The geometric separation argument for either sign of the actual
size-selection run. Negating the direction order preserves the required
absolute slope distances; physical boxes keep their original coordinates. -/
noncomputable section
open Set
namespace LipschitzHilbert

private theorem signed_chronology {α : Type*} {R : α → α → Prop} {xs : List α}
    (h : xs.Pairwise R) {a b : α} (ha : a∈xs) (hb : b∈xs) :
    a=b ∨ R a b ∨ R b a := by
  induction xs with
  | nil => simp only [List.not_mem_nil] at ha
  | cons x xs ih =>
    obtain ⟨hx,ht⟩ := List.pairwise_cons.mp h
    rcases List.mem_cons.mp ha with rfl | hax
    · rcases List.mem_cons.mp hb with rfl | hbx
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (hx _ hbx))
    · rcases List.mem_cons.mp hb with rfl | hbx
      · exact Or.inr (Or.inr (hx _ hax))
      · exact ih ht hax hbx

namespace PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

 theorem sizeDirection_sub (negative : Bool) (x y : ℝ) :
    sizeDirection negative (x-y)=sizeDirection negative x-sizeDirection negative y := by
  cases negative
  · rfl
  · simp only [sizeDirection,ite_true]
    ring

 theorem abs_sizeDirection_sub (negative : Bool) (x y : ℝ) :
    |sizeDirection negative x-sizeDirection negative y|=|x-y| := by
  cases negative
  · rfl
  · simp only [sizeDirection,ite_true]
    rw [show -x - -y=-(x-y) by ring,abs_neg]

namespace SizeStoppingRun
variable {P : PacketLatticeData N κ Label Item} {negative : Bool}
  {w cb tau sigma epsilon A : ℝ}
  {cell : ∀ j, P.labels j → ℤ} {grid : ℤ}
  {c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ}
  {initial remaining : Finset P.PacketIndex} {tops : List SlopeBox}

theorem selected_boxes_disjoint_signed
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining)
    (hw : 0<w) (hcb : 0<cb) (t K C : ℝ) (hK : 0≤K) (hC : 0≤C)
    (hA : 2*K*(1+C)+1/2≤A)
    (p p' : SlopeBox × Finset P.PacketIndex)
    (hp : p∈P.sizeSelectionRecords negative w cb A cell grid initial tops)
    (hp' : p'∈P.sizeSelectionRecords negative w cb A cell grid initial tops)
    (q q' : P.PacketIndex) (hq : q∈p.2) (hq' : q'∈p'.2)
    (hlen : P.length q.1≤P.length q'.1)
    (hnear : |P.rowSlope q.1 q.2.1-t|≤cb*(w/P.length q.1)/4)
    (htopnear : |p'.1.slope-t|≤cb*(w/P.length q.1)/4)
    (htopscaled : |p'.1.slope-t| * P.length q'.1≤C*P.width)
    (hepsilon : epsilon≤cb*(w/P.length q.1)/4)
    (hmargin : p'.1.slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) :
    Disjoint (densitySpatialBox (P.directionBox t q) K)
      (densitySpatialBox (P.directionBox t q') K) := by
  have hgeom := h.records_geometry p hp
  have hgeom' := h.records_geometry p' hp'
  have hqgeom := hgeom.2.2 q hq
  have hqgeom' := hgeom'.2.2 q' hq'
  have hsep : sizeDirection negative (P.rowSlope q.1 q.2.1)+cb*(w/P.length q.1)≤
      sizeDirection negative p.1.slope := by
    have hs := hqgeom.2.2.2
    rw [sizeDirection_sub,mul_div_assoc] at hs
    linarith
  have hn : |sizeDirection negative (P.rowSlope q.1 q.2.1)-sizeDirection negative t|≤
      cb*(w/P.length q.1)/4 := by simpa only [abs_sizeDirection_sub] using hnear
  have htn : |sizeDirection negative p'.1.slope-sizeDirection negative t|≤
      cb*(w/P.length q.1)/4 := by simpa only [abs_sizeDirection_sub] using htopnear
  apply Set.disjoint_left.mpr
  intro z hz hz'
  rcases signed_chronology h.records_order hp hp' with heq | horder | horder
  · rw [heq] at hsep
    have hleft := (abs_le.mp hn).1
    have hright := (abs_le.mp htn).2
    have hpos := mul_pos hcb (div_pos hw (P.length_pos q.1))
    linarith
  · have ho := horder.1
    exact selected_direction_order_contradiction _ _ _ _ _ _ _
      (div_pos hw (P.length_pos q.1)) hcb hn hsep htn hepsilon ho
  · have hcenters := common_direction_center_bounds
      (P.actualX q.1 q.2.1 q.2.2) (P.actualZ q.1 q.2.1 q.2.2)
      (P.actualX q'.1 q'.2.1 q'.2.2) (P.actualZ q'.1 q'.2.1 q'.2.2)
      t (P.length q.1) (P.length q'.1) P.width K hlen hK z
      hz.1 hz.2 hz'.1 hz'.2
    have hcenter := center_in_enlarged_selecting_top p'.1
      (P.actualX q.1 q.2.1 q.2.2) (P.actualZ q.1 q.2.1 q.2.2)
      (P.actualX q'.1 q'.2.1 q'.2.2) (P.actualZ q'.1 q'.2.1 q'.2.2)
      t (P.length q'.1) P.width K C A P.width_pos hK hC
      hqgeom'.1 hgeom'.1 hqgeom'.2.1 hcenters.1 hcenters.2 htopscaled hA
    exact horder.2 q hq ⟨hlen.trans hqgeom'.1,hcenter,hmargin⟩


end SizeStoppingRun
end PacketLatticeData
end LipschitzHilbert

end

end OAI
