import OAI.Combinatorics.BalancedRyser.Incidence.CandidateIncidenceProbability

namespace OAI

noncomputable section
open Filter
open scoped Topology Classical

namespace Balanced.CandidateIncidenceTests

universe u

theorem tendsto_candidateGraphGood_of_incidence
    (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop)
    (c C : ℝ) (hC : 0 ≤ C)
    (hsize : Tendsto (fun n => offsetEventProbability (F := F n)
      {M | SizeGood M c}) atTop (𝓝 1))
    (hsmall : Tendsto (fun n => offsetEventProbability (F := F n)
      {M | SmallGood M (Nat.ceil ((Fintype.card (F n) : ℝ) ^ (1 / 100 : ℝ)))})
      atTop (𝓝 1))
    (hglobal : Tendsto (fun n => offsetEventProbability (F := F n)
      {M | GlobalGood M C}) atTop (𝓝 1)) :
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | CandidateGraphGood M c (2 * C + 11)}) atTop (𝓝 1) := by
  have h₁ := tendsto_pmf_outerReal_inter_of_good (fun n => offsetLaw (F n))
    (fun _ => {M | SizeGood M c})
    (fun n => {M | SmallGood M (Nat.ceil ((Fintype.card (F n) : ℝ) ^ (1 / 100 : ℝ)))})
    hsize hsmall
  have h₂ := tendsto_pmf_outerReal_inter_of_good (fun n => offsetLaw (F n))
    (fun n => {M | SizeGood M c} ∩
      {M | SmallGood M (Nat.ceil ((Fintype.card (F n) : ℝ) ^ (1 / 100 : ℝ)))})
    (fun _ => {M | GlobalGood M C}) h₁ hglobal
  have h₃ := tendsto_pmf_outerReal_inter_of_good (fun n => offsetLaw (F n))
    (fun n => ({M | SizeGood M c} ∩
      {M | SmallGood M (Nat.ceil ((Fintype.card (F n) : ℝ) ^ (1 / 100 : ℝ)))}) ∩
      {M | GlobalGood M C})
    (fun _ => {M | CandidateProbability.GeometricGood M}) h₂
    (CandidateProbability.tendsto_geometricGood F hq)
  obtain ⟨N, hN⟩ := exists_threshold_graphGood.{u} C hC
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h₃ tendsto_const_nhds
  · filter_upwards [hq.eventually (eventually_ge_atTop N)] with n hn
    apply pmf_outerReal_mono (offsetLaw (F n))
    rintro M ⟨⟨⟨hs, hm⟩, hg⟩, hgeo⟩
    exact hN (F n) hn M c hs hm hg hgeo.1 hgeo.2
  · apply Eventually.of_forall
    intro n
    let : MeasurableSpace (MergedPairs (F n)) := ⊤
    let : MeasurableSingletonClass (MergedPairs (F n)) := ⟨fun _ => trivial⟩
    rw [LineOccupancy.offsetEventProbability_eq_real]
    exact MeasureTheory.measureReal_le_one

theorem candidateGraphResult_of_incidence_estimates (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C)
    (hsize : ∀ (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
      [∀ n, DecidableEq (F n)],
      Tendsto (fun n => Fintype.card (F n)) atTop atTop →
      Tendsto (fun n => offsetEventProbability (F := F n) {M | SizeGood M c})
        atTop (𝓝 1))
    (hsmall : ∀ (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
      [∀ n, DecidableEq (F n)],
      Tendsto (fun n => Fintype.card (F n)) atTop atTop →
      Tendsto (fun n => offsetEventProbability (F := F n)
        {M | SmallGood M (Nat.ceil ((Fintype.card (F n) : ℝ) ^ (1 / 100 : ℝ)))})
        atTop (𝓝 1))
    (hglobal : ∀ (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
      [∀ n, DecidableEq (F n)],
      Tendsto (fun n => Fintype.card (F n)) atTop atTop →
      Tendsto (fun n => offsetEventProbability (F := F n) {M | GlobalGood M C})
        atTop (𝓝 1)) : CandidateGraphResult.{u} := by
  refine ⟨c, 2 * C + 11, hc, by linarith, ?_⟩
  intro F _ _ _ hq
  have hgood := tendsto_candidateGraphGood_of_incidence F hq c C hC
    (hsize F hq) (hsmall F hq) (hglobal F hq)
  exact ⟨hgood, tendsto_candidateGood_and_distinct F hq c (2 * C + 11) hgood⟩

end Balanced.CandidateIncidenceTests

end

end OAI
