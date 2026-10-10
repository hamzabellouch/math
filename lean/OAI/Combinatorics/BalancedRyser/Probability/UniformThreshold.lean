import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import OAI.Combinatorics.BalancedRyser.Candidates.Candidates

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Filter Topology

theorem uniform_threshold_of_growing_sequences {X : Type*} (size : X → ℕ) (P : X → Prop)
    (h : ∀ x : ℕ → X, Tendsto (fun n => size (x n)) atTop atTop →
      ∀ᶠ n in atTop, P (x n)) :
    ∃ N : ℕ, ∀ x : X, N ≤ size x → P x := by
  classical
  by_contra hn
  push Not at hn
  choose x hsize hbad using hn
  have ht : Tendsto (fun n => size (x n)) atTop atTop :=
    tendsto_atTop_mono hsize tendsto_id
  obtain ⟨n, hn⟩ := (h x ht).exists
  exact hbad n hn

theorem uniform_metric_threshold_of_growing_sequences
    {X Y : Type*} [PseudoMetricSpace Y] (size : X → ℕ) (f : X → Y) (y : Y)
    (h : ∀ x : ℕ → X, Tendsto (fun n => size (x n)) atTop atTop →
      Tendsto (fun n => f (x n)) atTop (𝓝 y)) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ x : X, N ≤ size x → dist (f x) y < ε := by
  apply uniform_threshold_of_growing_sequences size
  intro x hx
  exact (Metric.tendsto_nhds.mp (h x hx)) ε hε

universe u

structure FiniteFieldPresentation where
  carrier : Type u
  field : Field carrier
  finite : Fintype carrier
  decidable : DecidableEq carrier

attribute [instance] FiniteFieldPresentation.field FiniteFieldPresentation.finite
  FiniteFieldPresentation.decidable

theorem candidate_graph_uniform_threshold (h : CandidateGraphResult.{u}) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F], N ≤ Fintype.card F →
        |offsetEventProbability (F := F) {M | CandidateGraphGood M c C} - 1| < ε ∧
        |offsetEventProbability (F := F)
          {M | CandidateGraphGood M c C ∧ DistinctConstituents M} - Real.exp (-1)| < ε := by
  obtain ⟨c, C, hc, hC, hseq⟩ := h
  refine ⟨c, C, hc, hC, ?_⟩
  intro ε hε
  let size : FiniteFieldPresentation.{u} → ℕ := fun A => Fintype.card A.carrier
  let P : FiniteFieldPresentation.{u} → Prop := fun A =>
    |offsetEventProbability (F := A.carrier) {M | CandidateGraphGood M c C} - 1| < ε ∧
    |offsetEventProbability (F := A.carrier)
      {M | CandidateGraphGood M c C ∧ DistinctConstituents M} - Real.exp (-1)| < ε
  have hev : ∀ A : ℕ → FiniteFieldPresentation.{u},
      Tendsto (fun n => size (A n)) atTop atTop → ∀ᶠ n in atTop, P (A n) := by
    intro A hA
    have hlim := hseq (fun n => (A n).carrier) hA
    have h₁ := (Metric.tendsto_nhds.mp hlim.1) ε hε
    have h₂ := (Metric.tendsto_nhds.mp hlim.2) ε hε
    simpa only [P, Real.dist_eq] using h₁.and h₂
  obtain ⟨N, hN⟩ := uniform_threshold_of_growing_sequences size P hev
  refine ⟨N, ?_⟩
  intro F hF hFin hDec hcard
  exact hN ⟨F, hF, hFin, hDec⟩ hcard

end Balanced

end OAI
