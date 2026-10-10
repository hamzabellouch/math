import OAI.Analysis.LipschitzFree.PortGraphs
import OAI.Analysis.LipschitzFree.StatePaths
import OAI.Analysis.LipschitzFree.SignedTests

namespace OAI

/-!
# Matched graph walks and exceptional record estimates
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.PortGraph
open scoped Classical
variable {X D S : Type*} (G : PortGraph X D)
    (compatible : X → S → Prop) (trans : S → S → Prop)

def Matched : X → S → List D → Prop
  | x, j, [] => compatible x j
  | x, j, e::w => compatible x j ∧ ∃ k, trans j k ∧ Matched (G.move x e) k w

theorem Matched.compat {x : X} {j : S} {w : List D}
    (h : G.Matched compatible trans x j w) : compatible x j := by
  cases w with
  | nil => exact h
  | cons e w => exact h.1

theorem Matched.take {x : X} {j : S} {w : List D}
    (h : G.Matched compatible trans x j w) (n : ℕ) :
    G.Matched compatible trans x j (w.take n) := by
  induction n generalizing x j w with
  | zero => exact h.compat
  | succ n ih =>
    cases w with
    | nil => exact h
    | cons e w =>
      obtain ⟨hx, k, hk, hw⟩ := h
      exact ⟨hx, k, hk, ih hw⟩

def Good (n : ℕ) (x : X) : Prop :=
  ∀ j w, w.length = n → G.Reduced w → ¬ G.Matched compatible trans x j w

theorem Good.length_lt {n : ℕ} {x : X} (hgood : G.Good compatible trans n x)
    {j : S} {w : List D} (hr : G.Reduced w) (hm : G.Matched compatible trans x j w) :
    w.length < n := by
  by_contra h
  have hn : n ≤ w.length := Nat.le_of_not_gt h
  apply hgood j (w.take n) (by simp [List.length_take, Nat.min_eq_left hn])
    (List.IsChain.take hr n)
  exact Matched.take G compatible trans hm n

def RecordLength (x : X) (e : D) (j : S) (t : ℕ) : Prop :=
  t = 0 ∨ ∃ w : List D, (e::w).length = t ∧ G.Reduced (e::w) ∧
    G.Matched compatible trans x j (e::w)

def record (n : ℕ) (x : X) (e : D) (j : S) : ℕ :=
  Nat.findGreatest (G.RecordLength compatible trans x e j) n

theorem record_spec (n : ℕ) (x : X) (e : D) (j : S) :
    G.RecordLength compatible trans x e j (G.record compatible trans n x e j) :=
  Nat.findGreatest_spec (Nat.zero_le n) (Or.inl rfl)

theorem record_le (n : ℕ) (x : X) (e : D) (j : S) :
    G.record compatible trans n x e j ≤ n := Nat.findGreatest_le _

theorem le_record {n : ℕ} {x : X} (hgood : G.Good compatible trans n x)
    {e : D} {j : S} {w : List D} (hr : G.Reduced (e::w))
    (hm : G.Matched compatible trans x j (e::w)) :
    (e::w).length ≤ G.record compatible trans n x e j :=
  Nat.le_findGreatest (Nat.le_of_lt (Good.length_lt G compatible trans hgood hr hm)) (Or.inr ⟨w, rfl, hr, hm⟩)

theorem record_extension {n : ℕ} {x : X} {e g : D} {j k : S}
    (hx : G.Good compatible trans n x)
    (hc : compatible x j) (hd : compatible (G.move x e) k) (ht : trans j k)
    (hg : g ≠ G.reverse e) :
    1 + G.record compatible trans n (G.move x e) g k ≤
      G.record compatible trans n x e j := by
  rcases G.record_spec compatible trans n (G.move x e) g k with hz | ⟨w, hw, hr, hm⟩
  · rw [hz]
    exact G.le_record compatible trans hx (List.isChain_singleton e) ⟨hc, k, ht, hd⟩
  · have hr' : G.Reduced (e::g::w) := List.isChain_cons_cons.mpr ⟨hg, hr⟩
    have hm' : G.Matched compatible trans x j (e::g::w) := ⟨hc, k, ht, hm⟩
    have hh := G.le_record compatible trans hx hr' hm'
    simpa only [List.length_cons, hw, Nat.add_comm] using hh

theorem matched_exceptional_endpoint {n : ℕ} {x : X} {e : D} {j k : S}
    (hx : G.Good compatible trans n x) (hy : G.Good compatible trans n (G.move x e))
    (hc : compatible x j) (hd : compatible (G.move x e) k)
    (ht : trans j k) (ht' : trans k j) :
    Exceptional (G.record compatible trans n x) e j ∨
      Exceptional (G.record compatible trans n (G.move x e)) (G.reverse e) k := by
  apply exceptional_of_extensions
  · intro g hg
    exact G.record_extension compatible trans hx hc hd ht hg
  · intro g hg
    have h := G.record_extension compatible trans hy hd
      (show compatible (G.move (G.move x e) (G.reverse e)) j by simpa only [G.move_reverse])
      ht' (show g ≠ G.reverse (G.reverse e) by simpa only [G.reverse_involutive e])
    simpa only [G.move_reverse] using h

end DiscreteFree.PortGraph
end

noncomputable section
namespace DiscreteFree.PortGraph
open scoped Classical
variable {X D S : Type*} (G : PortGraph X D)
    (compatible : X → S → Prop) (trans : S → S → Prop)

theorem Matched.exists_based {x : X} {j : S} {w : List D}
    (h : G.Matched compatible trans x j w) :
    ∃ p : StatePaths.Based trans j w.length, ∀ i : Fin (w.length+1),
      compatible (G.walk x (w.take i.val)) (StatePaths.vertex trans j p i) := by
  induction w generalizing x j with
  | nil =>
    refine ⟨PUnit.unit, fun i => ?_⟩
    simpa [StatePaths.vertex, PortGraph.Matched] using h
  | cons e w ih =>
    obtain ⟨hc, k, hk, hm⟩ := h
    obtain ⟨p, hp⟩ := ih hm
    refine ⟨⟨⟨k, hk⟩, p⟩, fun i => ?_⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · change compatible x j
      exact hc
    · change compatible (G.walk (G.move x e) (w.take i.val)) (StatePaths.vertex trans k p i)
      exact hp i

end DiscreteFree.PortGraph
end

end

end OAI
