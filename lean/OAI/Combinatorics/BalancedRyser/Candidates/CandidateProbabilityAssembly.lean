import OAI.Combinatorics.BalancedRyser.Candidates.CandidateDistinctLaw
import OAI.Combinatorics.BalancedRyser.Selection.InitialOccupancyUniform

namespace OAI

namespace Balanced.CandidateProbability

open Filter
open scoped Topology

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def GraphAssertions (M : MergedPairs F) (c C : ℝ) : Prop :=
  let q : ℝ := Fintype.card F
  (∀ s, c * q ≤ ((candidateSlot M s).card : ℝ) ∧
    (candidateSlot M s).card ≤ Fintype.card F) ∧
  (∀ v ∈ candidateVertices M,
    ((candidateNeighbors M v).card : ℝ) ≤ C * q ∧
    ∀ s, (((candidateNeighbors M v) ∩ candidateSlot M s).card : ℝ) ≤ q ^ (1 / 8 : ℝ)) ∧
  (∀ v ∈ candidateVertices M, ∃ J : Finset (CandidateVertex F),
    J ⊆ candidateVertices M ∧ (J.card : ℝ) ≤ q ^ (1 / 8 : ℝ) ∧
    (∀ w ∈ J, CandidateAdjacent M v w ∨ w.1 = v.1) ∧
    ∀ w ∈ candidateVertices M, w ∉ J →
      (((candidateNeighbors M v) ∩ candidateNeighbors M w).card : ℝ) ≤ q ^ (1 / 8 : ℝ))

def GeometricGood (M : MergedPairs F) : Prop :=
  (∀ p, sampledMultiplicity M p ≤ ⌈Real.log (Fintype.card F : ℝ)⌉₊) ∧
  (∀ l, l ∉ initialDeletedLines M →
    (1 / 5 : ℝ) * Fintype.card F ≤ ((linePoints l ∩ initiallyRetained M).card : ℝ))

theorem graphGood_iff (M : MergedPairs F) (c C : ℝ) :
    CandidateGraphGood M c C ↔ GraphAssertions M c C ∧ GeometricGood M := by
  simp only [CandidateGraphGood, GraphAssertions, GeometricGood, and_assoc]

theorem tendsto_geometricGood
    (F : ℕ → Type*) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability (F := F n) {M | GeometricGood M})
      atTop (𝓝 1) := by
  have h := tendsto_pmf_outerReal_inter_of_good (fun n => offsetLaw (F n))
    (fun n => {M | ∀ p, sampledMultiplicity M p ≤
      ⌈Real.log (Fintype.card (F n) : ℝ)⌉₊})
    (fun n => {M | ∀ l, l ∉ initialDeletedLines M →
      (1 / 5 : ℝ) * Fintype.card (F n) ≤
        ((linePoints l ∩ initiallyRetained M).card : ℝ)})
    (tendsto_sampledMultiplicity_good F hq)
    (LineOccupancy.tendsto_initial_occupancy F hq)
  simpa only [offsetEventProbability, ← Set.ofPred_and, GeometricGood] using h

theorem tendsto_geometricGood_and_distinct
    (F : ℕ → Type*) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | GeometricGood M ∧ DistinctConstituents M})
      atTop (𝓝 (Real.exp (-1))) := by
  have h := tendsto_pmf_outerReal_inter_of_good (fun n => offsetLaw (F n))
    (fun _ => {M | DistinctConstituents M}) (fun _ => {M | GeometricGood M})
    (tendsto_offsetProbability_distinctConstituents F hq) (tendsto_geometricGood F hq)
  simpa only [offsetEventProbability, ← Set.ofPred_and, and_comm] using h

theorem tendsto_candidateGraphGood_of_graphAssertions
    (F : ℕ → Type*) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) (c C : ℝ)
    (hgraph : Tendsto (fun n => offsetEventProbability (F := F n)
      {M | GraphAssertions M c C}) atTop (𝓝 1)) :
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | CandidateGraphGood M c C}) atTop (𝓝 1) := by
  have h := tendsto_pmf_outerReal_inter_of_good (fun n => offsetLaw (F n))
    (fun _ => {M | GraphAssertions M c C}) (fun _ => {M | GeometricGood M})
    hgraph (tendsto_geometricGood F hq)
  simpa only [offsetEventProbability, ← Set.ofPred_and, ← graphGood_iff] using h

universe u

theorem candidateGraphResult_of_graphAssertions
    (hgraph : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
        [∀ n, DecidableEq (F n)],
        Tendsto (fun n => Fintype.card (F n)) atTop atTop →
        Tendsto (fun n => offsetEventProbability (F := F n)
          {M | GraphAssertions M c C}) atTop (𝓝 1)) :
    CandidateGraphResult.{u} := by
  obtain ⟨c, C, hc, hC, hgraph⟩ := hgraph
  refine ⟨c, C, hc, hC, ?_⟩
  intro F _ _ _ hq
  have hgood := tendsto_candidateGraphGood_of_graphAssertions F hq c C (hgraph F hq)
  exact ⟨hgood, tendsto_candidateGood_and_distinct F hq c C hgood⟩

end
end Balanced.CandidateProbability

end OAI
