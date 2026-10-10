import Mathlib
import OAI.Probability.LatticeSurface.Convexity.BoundedBase
import OAI.Probability.LatticeSurface.Geometry.CapReflection
import OAI.Probability.LatticeSurface.Geometry.CapSplit
import OAI.Probability.LatticeSurface.Geometry.CapUnpin
import OAI.Probability.LatticeSurface.Geometry.CapWeld

namespace OAI

noncomputable section

open MeasureTheory Set

open scoped ENNReal

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

def squash (w v x : V) : V := if x = w then v else x

def contract (G : SimpleGraph V) (w v : V) : SimpleGraph V := G.map (squash w v)

lemma graph_constraint_map (G : SimpleGraph V) (f : V → V) (h : V → ℝ) :
    (∀ x y, (G.map f).Adj x y → |h x-h y| ≤ 1) ↔
      (∀ x y, G.Adj x y → |h (f x)-h (f y)| ≤ 1) := by
  constructor
  · intro hh x y hxy
    by_cases he : f x = f y
    · simp [he]
    · exact hh _ _ (SimpleGraph.map_adj_apply' hxy he)
  · rintro hh x y ⟨hne,a,b,hab,rfl,rfl⟩
    exact hh a b hab

lemma contracted_body (G : SimpleGraph V) (pins : Set V) (w v : V) :
    conditionalBody (contract G w v) pins (fun _ => 0) = weldBody G pins w v := by
  ext h
  rw [conditionalBody, mem_ofPred_eq, contract, graph_constraint_map]
  have hf : ∀ x, restore pins (fun _ => 0) h (squash w v x) = weldHeight pins w v h x := by
    intro x
    by_cases hx : x = w <;> simp [squash, weldHeight, hx]
  simp only [hf, weldBody, mem_ofPred_eq]

lemma degree_map_singleton [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V → V) (a : V) (hf : ∀ x, f x = a → x = a) :
    (G.map f).degree a ≤ G.degree a := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  refine (Finset.card_le_card (t := (G.neighborFinset a).image f) ?_).trans (Finset.card_image_le)
  intro y hy
  have hh : (G.map f).Adj a y := by simpa using hy
  rcases hh with ⟨hne,x,z,hxz,hxa,hzy⟩
  have hxa' := hf x hxa
  subst x
  exact Finset.mem_image.mpr ⟨z, by simpa using hxz, hzy⟩

def collapse (W : Finset V) (r : V → V) (x : V) : V := if x ∈ W then r x else x

lemma collapse_empty (r : V → V) : collapse ∅ r = id := by
  funext x; simp [collapse]

lemma collapse_insert {W : Finset V} {w : V} {r : V → V}
    (hw : w ∉ W) (hr : ∀ x ∈ insert w W, r x ∉ insert w W) :
    collapse (insert w W) r = squash w (r w) ∘ collapse W r := by
  classical
  funext x
  have hrr : ∀ y ∈ insert w W, r y ≠ w := fun y hy hh => hr y hy (by simp [hh])
  by_cases hxw : x = w
  · subst x; simp [collapse, squash, hw]
  · by_cases hx : x ∈ W
    · have hn := hrr x (Finset.mem_insert_of_mem hx)
      simp [collapse, squash, hx, hxw, hn]
    · simp [collapse, squash, hx, hxw]

lemma collapse_unique [DecidableEq V] {W : Finset V} {w : V} {r : V → V}
    (_hw : w ∉ W) (hr : ∀ x ∈ W, r x ≠ w) :
    ∀ x, collapse W r x = w → x = w := by
  intro x hh
  by_cases hx : x ∈ W
  · exact False.elim (hr x hx (by simpa [collapse, hx] using hh))
  · simpa [collapse, hx] using hh

lemma volume_graph_body_congr [Fintype V] {G H : SimpleGraph V} (h : G = H)
    (pins : Set V) (b : V → ℝ) :
    volume (conditionalBody G pins b) = volume (conditionalBody H pins b) := by rw [h]

theorem volume_collapsed_body_le [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (pins : Set V) (W : Finset V) (r : V → V) (D : ℕ)
    (hwp : ∀ w ∈ W, w ∉ pins) (hr : ∀ w ∈ W, r w ∉ W)
    (hd : ∀ w ∈ W, G.degree w ≤ D) :
    volume (conditionalBody (G.map (collapse W r)) (pins ∪ (W : Set V)) (fun _ => 0)) ≤
      (2 ^ D) ^ W.card * volume (conditionalBody G pins (fun _ => 0)) := by
  classical
  induction W using Finset.induction_on with
  | empty =>
    have hg : G.map (collapse ∅ r) = G := by simp [collapse_empty]
    rw [hg, volume_body_pin_congr G (show pins ∪ (∅ : Finset V) = pins by simp) _]
    simp
  | @insert w W hw ih =>
    have hwp' : ∀ x ∈ W, x ∉ pins := fun x hx => hwp x (Finset.mem_insert_of_mem hx)
    have hr' : ∀ x ∈ W, r x ∉ W := fun x hx ht => hr x (Finset.mem_insert_of_mem hx)
      (Finset.mem_insert_of_mem ht)
    have hd' : ∀ x ∈ W, G.degree x ≤ D := fun x hx => hd x (Finset.mem_insert_of_mem hx)
    have ihh := ih hwp' hr' hd'
    let H := G.map (collapse W r)
    let P : Set V := pins ∪ (insert w W : Finset V)
    have hwP : w ∈ P := Or.inr (by simp)
    have hvw : r w ≠ w := fun he => hr w (by simp) (by simp [he])
    have heG : G.map (collapse (insert w W) r) = contract H w (r w) := by
      rw [collapse_insert hw hr]
      exact (SimpleGraph.map_map _ _ _).symm
    have hPr : P \ {w} = pins ∪ (W : Set V) := by
      ext x
      have hnp := hwp w (by simp)
      simp only [P, mem_sdiff, mem_union, Finset.mem_coe, Finset.mem_insert, mem_singleton_iff]
      constructor
      · rintro ⟨hp | hx,hn⟩
        · exact Or.inl hp
        · exact Or.inr (hx.resolve_left hn)
      · intro hh
        refine ⟨?_, ?_⟩
        · exact hh.elim Or.inl (fun hx => Or.inr (Or.inr hx))
        · intro he
          subst x
          exact hh.elim hnp hw
    have hdeg : H.degree w ≤ D :=
      (degree_map_singleton G (collapse W r) w (collapse_unique hw
        (fun x hx hh => hr x (Finset.mem_insert_of_mem hx) (by simp [hh])))).trans
          (hd w (by simp))
    have hv := volume_weld_le H P w (r w) hwP hvw
    rw [← contracted_body] at hv
    rw [volume_body_pin_congr H hPr _] at hv
    calc
      volume (conditionalBody (G.map (collapse (insert w W) r))
          (pins ∪ (insert w W : Finset V)) (fun _ => 0)) =
        volume (conditionalBody (contract H w (r w)) P (fun _ => 0)) :=
          volume_graph_body_congr heG _ _
      _ ≤ 2 ^ H.degree w * volume (conditionalBody H (pins ∪ (W : Set V)) (fun _ => 0)) := hv
      _ ≤ 2 ^ D * ((2 ^ D) ^ W.card * volume (conditionalBody G pins (fun _ => 0))) := by
        apply mul_le_mul' ?_ ihh
        exact pow_le_pow_right' (by norm_num) hdeg
      _ = _ := by rw [Finset.card_insert_of_notMem hw, pow_succ]; ring

end ExtremalEdges

end

end OAI
