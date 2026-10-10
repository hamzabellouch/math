import Mathlib
import OAI.Combinatorics.UniformKServer.HeavyPilot

namespace OAI

                                    
section

/-! The literal deterministic heavy-center recursion of companion §07.
The update decision depends only on the request, posterior, and old centers,
not on any radius, lifetime, allocation, or rounding variable. -/
noncomputable section
namespace UniformKServer.HeavySchedule
open Finset
open scoped Classical
variable {X : Type*} [MetricSpace X]

def Separated (r : ℝ) (H : Finset X) : Prop :=
  ∀ a ∈ H, ∀ b ∈ H, a ≠ b → 100*r < dist a b

def trigger (r : ℝ) (h : Prop) (H : Finset X) (x : X) : Prop :=
  h ∧ ∀ c ∈ H, 8*r < dist x c

def step (r : ℝ) (h : Prop) (H : Finset X) (x : X) : Finset X :=
  if trigger r h H x then HeavyPilot.updateCenters r H x else H

def centers (r : ℝ) (h : ℕ → Prop) (x : ℕ → X) : ℕ → Finset X
  | 0 => ∅
  | t+1 => step r (h t) (centers r h x t) (x t)

theorem update_separated (r : ℝ) (H : Finset X) (x : X) (hs : Separated r H) :
    Separated r (HeavyPilot.updateCenters r H x) := by
  intro a ha b hb hne
  simp only [HeavyPilot.updateCenters,mem_insert,mem_filter] at ha hb
  rcases ha with rfl | ha
  · rcases hb with rfl | hb
    · exact (hne rfl).elim
    · exact hb.2
  · rcases hb with rfl | hb
    · simpa only [dist_comm] using ha.2
    · exact hs a ha.1 b hb.1 hne

theorem step_separated (r : ℝ) (h : Prop) (H : Finset X) (x : X) (hs : Separated r H) :
    Separated r (step r h H x) := by
  unfold step
  split_ifs
  · exact update_separated r H x hs
  · exact hs

theorem centers_separated (r : ℝ) (h : ℕ → Prop) (x : ℕ → X) (t : ℕ) :
    Separated r (centers r h x t) := by
  induction t with
  | zero => intro a ha; exact (notMem_empty a ha).elim
  | succ t ih => exact step_separated r (h t) _ _ ih

theorem coverage (r : ℝ) (hr : 0 ≤ r) (h : Prop) (hh : h) (H : Finset X) (x : X) :
    ∃ c ∈ step r h H x, dist x c ≤ 8*r := by
  by_cases hu : trigger r h H x
  · refine ⟨x,?_,?_⟩
    · simp only [step,ite_eq_left hu,HeavyPilot.updateCenters,mem_insert_self]
    · simp only [dist_self]; positivity
  · have hn : ¬∀ c ∈ H, 8*r < dist x c := fun hf => hu ⟨hh,hf⟩
    push Not at hn
    obtain ⟨c,hc,hd⟩ := hn
    exact ⟨c,by simpa only [step,ite_eq_right hu] using hc,hd⟩

theorem centers_coverage (r : ℝ) (hr : 0 ≤ r) (h : ℕ → Prop) (x : ℕ → X)
    (t : ℕ) (hh : h t) : ∃ c ∈ centers r h x (t+1), dist (x t) c ≤ 8*r :=
  coverage r hr (h t) hh _ _

theorem intersect_unique (r : ℝ) (hr : 0 ≤ r) (H : Finset X) (hs : Separated r H)
    (x a b : X) (ha : a ∈ H) (hb : b ∈ H)
    (hax : dist x a ≤ 40*r) (hbx : dist x b ≤ 40*r) : a=b := by
  by_contra hn
  have hh := hs a ha b hb hn
  have ht := dist_triangle a x b
  rw [dist_comm a x] at ht
  nlinarith

theorem near_unique (r : ℝ) (hr : 0 ≤ r) (H : Finset X) (hs : Separated r H)
    (y a b : X) (ha : a ∈ H) (hb : b ∈ H)
    (hay : dist y a ≤ 7*r) (hby : dist y b ≤ 7*r) : a=b :=
  intersect_unique r hr H hs y a b ha hb (by nlinarith) (by nlinarith)

theorem intersection_displacement (r : ℝ) (a b z : X)
    (ha : dist a z ≤ 20*r) (hb : dist b z ≤ 20*r) : dist a b ≤ 40*r := by
  have ht := dist_triangle a z b
  rw [dist_comm z b] at ht
  linarith

end UniformKServer.HeavySchedule

end


end

end OAI
