import OAI.Combinatorics.BalancedRyser.Candidates.CandidateProbabilityAssembly
import OAI.Combinatorics.BalancedRyser.Probability.UniformThreshold

namespace OAI

namespace Balanced.CandidateProbability

open Filter Topology
universe u

theorem geometric_distinct_uniform_threshold (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      N ≤ Fintype.card F →
      |offsetEventProbability (F := F)
        {M | GeometricGood M ∧ DistinctConstituents M} - Real.exp (-1)| < ε := by
  let size : FiniteFieldPresentation.{u} → ℕ := fun A => Fintype.card A.carrier
  let P : FiniteFieldPresentation.{u} → Prop := fun A =>
    |offsetEventProbability (F := A.carrier)
      {M | GeometricGood M ∧ DistinctConstituents M} - Real.exp (-1)| < ε
  have hev : ∀ A : ℕ → FiniteFieldPresentation.{u},
      Tendsto (fun n => size (A n)) atTop atTop → ∀ᶠ n in atTop, P (A n) := by
    intro A hA
    have hlim := tendsto_geometricGood_and_distinct (fun n => (A n).carrier) hA
    simpa only [P, Real.dist_eq] using (Metric.tendsto_nhds.mp hlim) ε hε
  obtain ⟨N, hN⟩ := uniform_threshold_of_growing_sequences size P hev
  refine ⟨N, ?_⟩
  intro F hF hFin hDec hcard
  exact hN ⟨F, hF, hFin, hDec⟩ hcard

theorem exists_geometric_good_distinct_uniform :
    ∃ N : ℕ, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      N ≤ Fintype.card F →
      ∃ M : MergedPairs F, GeometricGood M ∧ DistinctConstituents M := by
  obtain ⟨N, hN⟩ := geometric_distinct_uniform_threshold.{u}
    (Real.exp (-1) / 2) (by positivity)
  refine ⟨N, ?_⟩
  intro F hF hFin hDec hcard
  have hnear := hN F hcard
  have hpos : 0 < offsetEventProbability (F := F)
      {M | GeometricGood M ∧ DistinctConstituents M} := by
    have hp := Real.exp_pos (-1 : ℝ)
    have hlower := (abs_lt.mp hnear).1
    linarith
  by_contra hn
  have hempty : {M : MergedPairs F | GeometricGood M ∧ DistinctConstituents M} = ∅ := by
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact fun hM => hn ⟨M, hM⟩
  simp [hempty, offsetEventProbability] at hpos

end Balanced.CandidateProbability

end OAI
