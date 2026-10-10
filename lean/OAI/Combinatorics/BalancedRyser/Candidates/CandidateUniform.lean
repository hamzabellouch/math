import OAI.Combinatorics.BalancedRyser.Candidates.CandidateProbabilityAssembly

namespace OAI

namespace Balanced.CandidateUniform

open Filter MeasureTheory
open scoped Topology

universe u v

theorem exists_uniform_lower_bound {α : Type v} (size : α → ℕ) (f : α → ℝ)
    (L b : ℝ) (hb : b < L)
    (h : ∀ a : ℕ → α, Tendsto (fun n => size (a n)) atTop atTop →
      Tendsto (fun n => f (a n)) atTop (𝓝 L)) :
    ∃ N : ℕ, ∀ a, N ≤ size a → b < f a := by
  classical
  by_contra hn
  push Not at hn
  choose a ha hfa using hn
  have hsize : Tendsto (fun n => size (a n)) atTop atTop :=
    tendsto_atTop_mono ha tendsto_id
  obtain ⟨n, hn⟩ := ((h a hsize).eventually_const_lt hb).exists
  exact (not_lt_of_ge (hfa n)) hn

private structure FieldPresentation where
  carrier : Type u
  field : Field carrier
  finite : Fintype carrier
  decidable : DecidableEq carrier

private def order (P : FieldPresentation.{u}) : ℕ :=
  @Fintype.card P.carrier P.finite

private noncomputable def goodMass (c C : ℝ) (P : FieldPresentation.{u}) : ℝ :=
  letI := P.field
  letI := P.finite
  letI := P.decidable
  offsetEventProbability (F := P.carrier)
    {M | CandidateGraphGood M c C ∧ DistinctConstituents M}

theorem exists_uniform_candidate_probability (h : CandidateGraphResult.{u}) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
        N ≤ Fintype.card F →
        Real.exp (-1) / 2 < offsetEventProbability (F := F)
          {M | CandidateGraphGood M c C ∧ DistinctConstituents M} := by
  classical
  obtain ⟨c, C, hc, hC, hseq⟩ := h
  have hlim : ∀ a : ℕ → FieldPresentation.{u},
      Tendsto (fun n => order (a n)) atTop atTop →
      Tendsto (fun n => goodMass c C (a n)) atTop (𝓝 (Real.exp (-1))) := by
    intro a ha
    let : ∀ n, Field ((a n).carrier) := fun n => (a n).field
    let : ∀ n, Fintype ((a n).carrier) := fun n => (a n).finite
    let : ∀ n, DecidableEq ((a n).carrier) := fun n => (a n).decidable
    exact (hseq (fun n => (a n).carrier) ha).2
  have hb : Real.exp (-1) / 2 < Real.exp (-1) := by
    have := Real.exp_pos (-1)
    linarith
  obtain ⟨N, hN⟩ := exists_uniform_lower_bound order (goodMass c C)
    (Real.exp (-1)) (Real.exp (-1) / 2) hb hlim
  refine ⟨c, C, hc, hC, N, ?_⟩
  intro F hF hfin hdec hcard
  exact hN ⟨F, hF, hfin, hdec⟩ hcard

theorem exists_uniform_candidate_witness (h : CandidateGraphResult.{u}) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
        N ≤ Fintype.card F → ∃ M : MergedPairs F,
          CandidateGraphGood M c C ∧ DistinctConstituents M := by
  classical
  obtain ⟨c, C, hc, hC, N, hN⟩ := exists_uniform_candidate_probability h
  refine ⟨c, C, hc, hC, N, ?_⟩
  intro F _ _ _ hcard
  have hp := hN F hcard
  by_contra hn
  have hempty : {M : MergedPairs F | CandidateGraphGood M c C ∧
      DistinctConstituents M} = ∅ := by
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact fun hM => hn ⟨M, hM⟩
  rw [hempty] at hp
  simp only [offsetEventProbability, measure_empty, ENNReal.toReal_zero] at hp
  have : 0 < Real.exp (-1) / 2 := by positivity
  linarith

end Balanced.CandidateUniform

end OAI
