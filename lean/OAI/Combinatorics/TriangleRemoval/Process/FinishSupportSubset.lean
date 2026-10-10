import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.Finish

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem finish_support_subset {n : ℕ} {G H : Graph n}
    (hH : H ∈ (finish G).support) : H ⊆ G :=
  evolve_support_subset G G.card hH

theorem uniform_edge_survival {n : ℕ} {G H : Graph n}
    (hG : G.Nonempty) (hH : H ⊆ G) :
    pmfMean (PMF.uniformOfFinset G hG) (fun e => if e ∈ H then 1 else 0) =
      (H.card : ℝ) / G.card := by
  classical
  rw [pmfMean_uniformOfFinset]
  congr 1
  rw [← Finset.sum_filter]
  have heq : G.filter (fun e => e ∈ H) = H := Finset.filter_mem_eq_inter |>.trans
    (Finset.inter_eq_right.mpr hH)
  simp [heq]

theorem uniform_two_edge_survival {n : ℕ} {G H : Graph n}
    (hG : G.Nonempty) (hH : H ⊆ G) :
    pmfMean (PMF.uniformOfFinset G hG) (fun e =>
      pmfMean (PMF.uniformOfFinset G hG) (fun f =>
        if e ∈ H ∧ f ∈ H then 1 else 0)) =
      (H.card : ℝ) ^ 2 / (G.card : ℝ) ^ 2 := by
  classical
  have hm (e : Finset (Fin n)) :
      pmfMean (PMF.uniformOfFinset G hG)
          (fun f => if e ∈ H ∧ f ∈ H then 1 else 0) =
        (if e ∈ H then 1 else 0) * ((H.card : ℝ) / G.card) := by
    by_cases he : e ∈ H
    · simpa [he] using uniform_edge_survival hG hH
    · simp [he]
  simp_rw [hm]
  rw [pmfMean_mul_const, uniform_edge_survival hG hH]
  ring

theorem terminal_first_edge_moment {n : ℕ} (G : Graph n) (hG : G.Nonempty) :
    pmfMean (finish G) (fun H =>
      pmfMean (PMF.uniformOfFinset G hG) (fun e => if e ∈ H then 1 else 0)) =
      pmfMean (finish G) (fun H => (H.card : ℝ)) / G.card := by
  classical
  calc
    _ = pmfMean (finish G) (fun H => (H.card : ℝ) / G.card) := by
      apply pmfMean_congr
      intro H hH
      exact uniform_edge_survival hG (finish_support_subset hH)
    _ = _ := by simp only [div_eq_mul_inv, pmfMean_mul_const]

theorem terminal_second_edge_moment {n : ℕ} (G : Graph n) (hG : G.Nonempty) :
    pmfMean (finish G) (fun H =>
      pmfMean (PMF.uniformOfFinset G hG) (fun e =>
        pmfMean (PMF.uniformOfFinset G hG) (fun f =>
          if e ∈ H ∧ f ∈ H then 1 else 0))) =
      pmfMean (finish G) (fun H => (H.card : ℝ) ^ 2) / (G.card : ℝ) ^ 2 := by
  classical
  calc
    _ = pmfMean (finish G) (fun H => (H.card : ℝ) ^ 2 / (G.card : ℝ) ^ 2) := by
      apply pmfMean_congr
      intro H hH
      exact uniform_two_edge_survival hG (finish_support_subset hH)
    _ = _ := by simp only [div_eq_mul_inv, pmfMean_mul_const]

theorem finite_coupling_event_bound {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF (α × β)) (A : α → Prop) (B : β → Prop)
    [DecidablePred A] [DecidablePred B] :
    |pmfMean (p.map Prod.fst) (fun a => if A a then 1 else 0) -
      pmfMean (p.map Prod.snd) (fun b => if B b then 1 else 0)| ≤
      pmfMean p (fun ab => if (A ab.1 ↔ B ab.2) then 0 else 1) := by
  rw [pmfMean_map, pmfMean_map, ← pmfMean_sub]
  apply abs_le.mpr
  constructor
  · have hh := pmfMean_mono p (f := fun ab => if (A ab.1 ↔ B ab.2) then 0 else 1)
        (g := fun ab => -((if A ab.1 then 1 else 0) - (if B ab.2 then 1 else 0)))
    have hmono : pmfMean p (fun ab =>
          -((if A ab.1 then 1 else 0) - (if B ab.2 then 1 else 0))) ≤
        pmfMean p (fun ab => if (A ab.1 ↔ B ab.2) then 0 else 1) := by
      apply pmfMean_mono
      intro ab _
      by_cases ha : A ab.1 <;> by_cases hb : B ab.2 <;> simp [ha, hb]
    have heq : pmfMean p (fun ab =>
          -((if A ab.1 then 1 else 0) - (if B ab.2 then 1 else 0))) =
        -pmfMean p (fun ab => (if A ab.1 then 1 else 0) - (if B ab.2 then 1 else 0)) := by
      simpa only [neg_one_mul] using (pmfMean_const_mul p (-1)
        (fun ab => (if A ab.1 then 1 else 0) - (if B ab.2 then 1 else 0)))
    rw [heq] at hmono
    linarith
  · apply pmfMean_mono
    intro ab _
    by_cases ha : A ab.1 <;> by_cases hb : B ab.2 <;> simp [ha, hb]

end SharpTerminalLeave

open Filter
open scoped BigOperators Topology

end

end OAI
