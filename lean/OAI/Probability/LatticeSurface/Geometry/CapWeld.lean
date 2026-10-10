import Mathlib
import OAI.Probability.LatticeSurface.Convexity.BoundedBase
import OAI.Probability.LatticeSurface.Geometry.CapReflection
import OAI.Probability.LatticeSurface.Geometry.CapSplit
import OAI.Probability.LatticeSurface.Geometry.CapUnpin

namespace OAI

noncomputable section

open MeasureTheory Set

open scoped ENNReal

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

def weldHeight (pins : Set V) (w v : V) (h : Free pins → ℝ) (x : V) : ℝ :=
  if x = w then restore pins (fun _ => 0) h v else restore pins (fun _ => 0) h x

def weldBody (G : SimpleGraph V) (pins : Set V) (w v : V) : Set (Free pins → ℝ) :=
  {h | ∀ x y, G.Adj x y → |weldHeight pins w v h x - weldHeight pins w v h y| ≤ 1}

lemma continuous_weldHeight [Fintype V] (pins : Set V) (w v x : V) :
    Continuous (fun h : Free pins → ℝ => weldHeight pins w v h x) := by
  by_cases hx : x = w <;> simp only [weldHeight, hx, ite_true, ite_false]
  · exact continuous_restore pins _ v
  · exact continuous_restore pins _ x

lemma closed_weldBody [Fintype V] (G : SimpleGraph V) (pins : Set V) (w v : V) :
    IsClosed (weldBody G pins w v) := by
  simp only [weldBody, Set.ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun _ =>
    isClosed_le ((continuous_weldHeight pins w v x).sub (continuous_weldHeight pins w v y)).abs
      continuous_const

lemma restore_boundary_congr (pins : Set V) {b c : V → ℝ}
    (hbc : ∀ x ∈ pins, b x = c x) (h : Free pins → ℝ) (x : V) :
    restore pins b h x = restore pins c h x := by
  by_cases hx : x ∈ pins <;> simp [restore, hx, hbc x]

lemma body_boundary_congr (G : SimpleGraph V) (pins : Set V) {b c : V → ℝ}
    (hbc : ∀ x ∈ pins, b x = c x) :
    conditionalBody G pins b = conditionalBody G pins c := by
  ext h
  simp only [conditionalBody, Set.mem_ofPred_eq, restore_boundary_congr pins hbc]

lemma weld_pinned (G : SimpleGraph V) (pins : Set V) (w v : V)
    (hw : w ∈ pins) (hv : v ∈ pins) :
    weldBody G pins w v = conditionalBody G pins (fun _ => 0) := by
  have hh : ∀ h x, weldHeight pins w v h x = restore pins (fun _ => 0) h x := by
    intro h x
    by_cases hx : x = w
    · subst x; simp [weldHeight, restore, hw, hv]
    · simp [weldHeight, hx]
  ext h
  simp only [weldBody, conditionalBody, Set.mem_ofPred_eq, hh]

def weldBoundary (w v : V) (a : ℝ) (x : V) : ℝ := if x = w ∨ x = v then a else 0

lemma weld_coordinate (pins : Set V) (w v : V) (hw : w ∈ pins) (hv : v ∉ pins)
    (h : Free (insert v pins) → ℝ) (a : ℝ) (x : V) :
    weldHeight pins w v ((splitCoordinate pins v hv).symm (h,a)) x =
      restore (insert v pins) (weldBoundary w v a) h x := by
  have hvw : v ≠ w := fun he => hv (he ▸ hw)
  rw [weldHeight, coordinate_restore, coordinate_restore]
  by_cases hxw : x = w
  · subst x
    simp [restore, hw, weldBoundary]
  · by_cases hxv : x = v
    · subst x
      simp [hxw, restore, weldBoundary]
    · by_cases hxp : x ∈ pins
      · simp [hxw, hxv, restore, hxp, weldBoundary]
      · simp [hxw, hxv, restore, hxp]

lemma weld_volume_coordinate [Fintype V] (G : SimpleGraph V) (pins : Set V)
    (w v : V) (hw : w ∈ pins) (hv : v ∉ pins) :
    volume (weldBody G pins w v) = ∫⁻ a : ℝ,
      volume (conditionalBody G (insert v pins) (weldBoundary w v a)) := by
  rw [volume_coordinate_slices pins v hv _ (closed_weldBody G pins w v).measurableSet]
  apply lintegral_congr
  intro a
  congr 1
  ext h
  simp only [weldBody, conditionalBody, Set.mem_ofPred_eq, weld_coordinate pins w v hw hv]

lemma weld_boundary_extreme (pins : Set V) (w v : V) (a : ℝ) :
    (∀ y ∈ pins, weldBoundary w v a y ≤ weldBoundary w v a w) ∨
    (∀ y ∈ pins, weldBoundary w v a w ≤ weldBoundary w v a y) := by
  rcases le_total 0 a with ha | ha
  · left; intro y hy; simp only [weldBoundary, true_or, ite_true]; split_ifs <;> linarith
  · right; intro y hy; simp only [weldBoundary, true_or, ite_true]; split_ifs <;> linarith

lemma weld_released_body (G : SimpleGraph V) (pins : Set V) (w v : V) (a : ℝ) :
    conditionalBody G ((insert v pins) \ {w}) (weldBoundary w v a) =
      conditionalBody G ((insert v pins) \ {w}) (Function.update (fun _ => 0) v a) := by
  apply body_boundary_congr
  intro x hx
  have hn : x ≠ w := hx.2
  by_cases hv : x = v
  · subst x; simp [weldBoundary]
  · simp [weldBoundary, hn, hv]

lemma volume_body_pin_congr [Fintype V] (G : SimpleGraph V) {p q : Set V}
    (hpq : p = q) (b : V → ℝ) :
    volume (conditionalBody G p b) = volume (conditionalBody G q b) := by
  subst q
  rfl

theorem volume_weld_le [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (pins : Set V) (w v : V) (hw : w ∈ pins) (hvw : v ≠ w) :
    volume (weldBody G pins w v) ≤
      2 ^ G.degree w * volume (conditionalBody G (pins \ {w}) (fun _ => 0)) := by
  classical
  by_cases hv : v ∈ pins
  · rw [weld_pinned G pins w v hw hv]
    exact volume_release_max_pin G pins w hw (fun _ => 0) (by simp)
  · have hvs : v ∉ pins \ {w} := fun h => hv h.1
    rw [weld_volume_coordinate G pins w v hw hv,
      volume_body_coordinate G (pins \ {w}) (fun _ => 0) v hvs,
      ← lintegral_const_mul' _ _ (by finiteness)]
    apply lintegral_mono
    intro a
    have hh := volume_release_extreme_pin G (insert v pins) w (Or.inr hw)
      (weldBoundary w v a) (weld_boundary_extreme (insert v pins) w v a)
    rw [weld_released_body] at hh
    have he : (insert v pins) \ {w} = insert v (pins \ {w}) := by
      ext x
      simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
      constructor
      · rintro ⟨h,hn⟩; exact h.elim Or.inl (fun hp => Or.inr ⟨hp,hn⟩)
      · rintro (h | h)
        · subst x; exact ⟨Or.inl rfl,hvw⟩
        · exact ⟨Or.inr h.1,h.2⟩
    rw [volume_body_pin_congr G he _] at hh
    exact hh

end ExtremalEdges

end

end OAI
