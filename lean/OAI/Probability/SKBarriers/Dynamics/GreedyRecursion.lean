import Mathlib
import OAI.Probability.SKBarriers.Dynamics.Crossing

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

structure GreedyRecord (n : ℕ) where
  refs : ℕ → Config n
  time : ℕ
  kept : Finset ℕ

def greedyRun {n : ℕ} (base : ℕ → Config n)
    (pick : ℕ → (ℕ → Config n) → ℕ → Config n)
    (x : ℕ → Config n) (r : ℕ → ℝ) (b : ℝ) (m : ℕ) : ℕ → GreedyRecord n
  | 0 => ⟨base,0,∅⟩
  | j+1 =>
    let s := greedyRun base pick x r b m j
    let w := pick j s.refs s.time
    ⟨Function.update s.refs j w,
      if j=0 then firstCrossing (fun k => overlap w (x k)) (r j) m
      else lastCrossing (fun k => overlap w (x k)) (r j) s.time,
      insert j (s.kept\s.kept.filter (fun i => b < |overlap (s.refs i) w|))⟩

def greedyReference {n : ℕ} (base : ℕ → Config n)
    (pick : ℕ → (ℕ → Config n) → ℕ → Config n)
    (x : ℕ → Config n) (r : ℕ → ℝ) (b : ℝ) (m j : ℕ) : Config n :=
  pick j (greedyRun base pick x r b m j).refs (greedyRun base pick x r b m j).time

theorem greedyRun_predictable {n : ℕ} (base : ℕ → Config n)
    (pick : ℕ → (ℕ → Config n) → ℕ → Config n)
    (x : ℕ → Config n) (r s : ℕ → ℝ) (b : ℝ) (m j : ℕ)
    (h : ∀ i < j, r i=s i) : greedyRun base pick x r b m j=greedyRun base pick x s b m j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hp := ih (fun i hi => h i (by omega))
    simp only [greedyRun,hp,h j (by omega)]

theorem greedyReference_predictable {n : ℕ} (base : ℕ → Config n)
    (pick : ℕ → (ℕ → Config n) → ℕ → Config n)
    (x : ℕ → Config n) (r s : ℕ → ℝ) (b : ℝ) (m j : ℕ)
    (h : ∀ i < j, r i=s i) : greedyReference base pick x r b m j=greedyReference base pick x s b m j := by
  unfold greedyReference
  rw [greedyRun_predictable base pick x r s b m j h]

theorem greedyRun_refs {n : ℕ} (base : ℕ → Config n)
    (pick : ℕ → (ℕ → Config n) → ℕ → Config n)
    (x : ℕ → Config n) (r : ℕ → ℝ) (b : ℝ) (m j i : ℕ) (hi : i < j) :
    (greedyRun base pick x r b m j).refs i=greedyReference base pick x r b m i := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases he : i=j
    · subst i
      simp only [greedyRun,Function.update_self]
      rfl
    · simpa only [greedyRun,Function.update_of_ne he] using ih (by omega)

theorem greedyRun_range {n : ℕ} (base : ℕ → Config n)
    (pick : ℕ → (ℕ → Config n) → ℕ → Config n)
    (x : ℕ → Config n) (r : ℕ → ℝ) (b : ℝ) (m j : ℕ) :
    ∀ i ∈ (greedyRun base pick x r b m j).kept, i < j := by
  induction j with
  | zero => simp [greedyRun]
  | succ j ih =>
    intro i hi
    simp only [greedyRun,Finset.mem_insert] at hi
    rcases hi with rfl | hi
    · omega
    · have := ih i (Finset.mem_sdiff.mp hi).1
      omega

def bankPick {n : ℕ} (pool : ℕ → Finset (Config n)) (fallback : ℕ → Config n)
    (B : ℕ) (x : ℕ → Config n) (t q : ℝ)
    (j : ℕ) (v : ℕ → Config n) (u : ℕ) : Config n :=
  if h : ∃ w ∈ pool j, q ≤ overlap w (x u) ∧
      ∀ i, j/B*B ≤ i → i < j → |overlap (v i) w| ≤ 3*t
  then h.choose else fallback j

theorem bankPick_mem {n : ℕ} (pool : ℕ → Finset (Config n)) (fallback : ℕ → Config n)
    (hf : ∀ j, fallback j ∈ pool j) (B : ℕ) (x : ℕ → Config n) (t q : ℝ)
    (j : ℕ) (v : ℕ → Config n) (u : ℕ) : bankPick pool fallback B x t q j v u ∈ pool j := by
  unfold bankPick
  split_ifs with h
  · exact h.choose_spec.1
  · exact hf j

theorem bankPick_spec {n : ℕ} (pool : ℕ → Finset (Config n)) (fallback : ℕ → Config n)
    (B : ℕ) (x : ℕ → Config n) (t q : ℝ)
    (j : ℕ) (v : ℕ → Config n) (u : ℕ)
    (h : ∃ w ∈ pool j, q ≤ overlap w (x u) ∧
      ∀ i, j/B*B ≤ i → i < j → |overlap (v i) w| ≤ 3*t) :
    q ≤ overlap (bankPick pool fallback B x t q j v u) (x u) ∧
      ∀ i, j/B*B ≤ i → i < j → |overlap (v i) (bankPick pool fallback B x t q j v u)| ≤ 3*t := by
  rw [bankPick,dite_eq_left h]
  exact h.choose_spec.2

end SK.Analytic

end
end

end OAI
