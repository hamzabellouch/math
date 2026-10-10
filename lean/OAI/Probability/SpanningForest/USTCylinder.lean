import OAI.Probability.SpanningForest.Definitions

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Topology

namespace Problem336

theorem ustCylinder_split (K : FiniteSubgraphCode)
    (A B : Finset EdgeCode) (e : EdgeCode) :
    ustCylinder K A B =
      ustCylinder K (insert e A) B + ustCylinder K A (insert e B) := by
  classical
  let S := (spanningTrees K).filter (fun T =>
    (∀ f ∈ A, f.1 ∈ T) ∧ (∀ f ∈ B, f.1 ∉ T))
  have hyes : (spanningTrees K).filter (fun T =>
      (∀ f ∈ insert e A, f.1 ∈ T) ∧ (∀ f ∈ B, f.1 ∉ T)) =
      S.filter (fun T => e.1 ∈ T) := by
    ext T
    simp only [S, Finset.mem_filter, Finset.forall_mem_insert]
    tauto
  have hno : (spanningTrees K).filter (fun T =>
      (∀ f ∈ A, f.1 ∈ T) ∧ (∀ f ∈ insert e B, f.1 ∉ T)) =
      S.filter (fun T => e.1 ∉ T) := by
    ext T
    simp only [S, Finset.mem_filter, Finset.forall_mem_insert]
    tauto
  unfold ustCylinder
  dsimp only
  change (S.card : ℝ≥0∞) / (spanningTrees K).card = _
  rw [hyes, hno]
  rw [← ENNReal.add_div]
  congr 1
  exact_mod_cast (Finset.card_filter_add_card_filter_not (s := S) (fun T => e.1 ∈ T)).symm

theorem ustCylinder_antitone_constraints (K : FiniteSubgraphCode)
    {A A' B B' : Finset EdgeCode} (hA : A ⊆ A') (hB : B ⊆ B') :
    ustCylinder K A' B' ≤ ustCylinder K A B := by
  classical
  unfold ustCylinder
  dsimp only
  apply ENNReal.div_le_div_right
  exact_mod_cast Finset.card_le_card (by
    intro T hT
    simp only [Finset.mem_filter] at hT ⊢
    exact ⟨hT.1, fun e he => hT.2.1 e (hA he),
      fun e he => hT.2.2 e (hB he)⟩)

theorem ustCylinder_partition (K : FiniteSubgraphCode)
    (A B C : Finset EdgeCode) :
    ustCylinder K A B =
      ∑ D ∈ C.powerset, ustCylinder K (A ∪ D) (B ∪ (C \ D)) := by
  classical
  induction C using Finset.induction_on generalizing A B with
  | empty => simp
  | @insert e C he ih =>
    rw [Finset.sum_powerset_insert he]
    have hfirst :
        (∑ D ∈ C.powerset,
          ustCylinder K (A ∪ D) (B ∪ (insert e C \ D))) =
          ustCylinder K A (insert e B) := by
      rw [ih A (insert e B)]
      apply Finset.sum_congr rfl
      intro D hD
      have heD : e ∉ D := fun h => he (Finset.mem_powerset.mp hD h)
      congr 1
      ext f
      by_cases hfe : f = e <;> simp [hfe, heD]
    have hsecond :
        (∑ D ∈ C.powerset,
          ustCylinder K (A ∪ insert e D) (B ∪ (insert e C \ insert e D))) =
          ustCylinder K (insert e A) B := by
      rw [ih (insert e A) B]
      apply Finset.sum_congr rfl
      intro D hD
      congr 1
      · ext f
        simp only [Finset.mem_union, Finset.mem_insert]
        tauto
      · ext f
        by_cases hfe : f = e <;> simp [hfe, he]
    rw [hfirst, hsecond, add_comm]
    exact ustCylinder_split K A B e

theorem ustCylinder_limit_split (H : ℕ → FiniteSubgraphCode)
    (p : Finset EdgeCode → Finset EdgeCode → ℝ≥0∞)
    (hlim : ∀ A B, Filter.Tendsto (fun n => ustCylinder (H n) A B)
      Filter.atTop (nhds (p A B)))
    (A B : Finset EdgeCode) (e : EdgeCode) :
    p A B = p (insert e A) B + p A (insert e B) := by
  apply tendsto_nhds_unique (hlim A B)
  simpa only [← ustCylinder_split] using
    (hlim (insert e A) B).add (hlim A (insert e B))

theorem ustCylinder_limit_partition (H : ℕ → FiniteSubgraphCode)
    (p : Finset EdgeCode → Finset EdgeCode → ℝ≥0∞)
    (hlim : ∀ A B, Filter.Tendsto (fun n => ustCylinder (H n) A B)
      Filter.atTop (nhds (p A B)))
    (A B C : Finset EdgeCode) :
    p A B = ∑ D ∈ C.powerset, p (A ∪ D) (B ∪ (C \ D)) := by
  apply tendsto_nhds_unique (hlim A B)
  have h := tendsto_finsetSum C.powerset (fun D _ => hlim (A ∪ D) (B ∪ (C \ D)))
  simpa only [← ustCylinder_partition] using h

end Problem336

end

end OAI
