import OAI.Probability.MatroidProphet.Reverse.Cost

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def reverseHazard (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ)
    (k : ℤ) (S : ℕ → Set α) : ℝ :=
  bitsFailure (reverseStayEvent M hE κ D S G k d h) q univ ∅

lemma reverseHazard_eq (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ)
    (k : ℤ) (S : ℕ → Set α) :
    reverseHazard M hE κ D G q d h k S = bitsExpectation q univ (fun C =>
      if d ∉ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k h then 1 else 0) := by
  unfold reverseHazard bitsFailure reverseStayEvent
  apply bitsExpectation_congr
  intro C hC
  simp only [empty_union]
  split_ifs <;> simp_all

lemma reverseHazard_nonneg (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) (d : α) (h : ℕ)
    (k : ℤ) (S : ℕ → Set α) : 0 ≤ reverseHazard M hE κ D G q d h k S :=
  bitsFailure_nonneg _ q hq0 hq1 _ _

lemma reverseHazard_le_one (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) (d : α) (h : ℕ)
    (k : ℤ) (S : ℕ → Set α) : reverseHazard M hE κ D G q d h k S ≤ 1 :=
  bitsFailure_le_one _ q hq0 hq1 _ _

lemma reverseHazard_mono (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) (d : α) (h : ℕ)
    {k l : ℤ} (hlk : l ≤ k) (S S' : ℕ → Set α) (hS : ∀ j, S' j ⊆ S j) :
    reverseHazard M hE κ D G q d h k S ≤ reverseHazard M hE κ D G q d h l S' := by
  rw [reverseHazard_eq, reverseHazard_eq]
  apply bitsExpectation_mono q hq0 hq1
  intro C hC
  have hn := reverseNominal_mono M hE κ D
    (fun i => (C : Set α) ∩ (G i : Set α)) _ S' S hlk (fun _ => Set.Subset.rfl) hS h
  by_cases he : d ∈ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S' l h
  · simp [he, hn he]
  · simp [he]
    split_ifs <;> norm_num

lemma reverseHazard_step_mono (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) (d : α) (h : ℕ)
    (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) (C : Finset α) :
    reverseHazard M hE κ D G q d h k S ≤
      reverseHazard M hE κ D G q d h (k-1) ((reverseStepTree M hE κ k D S G n).run C) :=
  reverseHazard_mono M hE κ D G q hq0 hq1 d h (by omega) S _
    (reverseStepTree_contracts M hE κ k D S G n closed C)

lemma reverseHazard_eq_step (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ) (d : α) (h : ℕ) (hh : h ≤ n)
    (k : ℤ) (S : ℕ → Set α) :
    reverseHazard M hE κ D G q d h k S = bitsExpectation q univ (fun C =>
      if d ∉ (reverseStepTree M hE κ k D S G n).run C h then 1 else 0) := by
  rw [reverseHazard_eq]
  apply bitsExpectation_congr
  intro C hC
  rw [reverseStepTree_run_coordinate M hE κ k D S G n hG C hh]

noncomputable def bandNonexitCost (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ)
    (p₀ upper : ℝ) (k : ℤ) (S S' : ℕ → Set α) : ℝ :=
  if p₀ ≤ reverseHazard M hE κ D G q d h k S ∧
      reverseHazard M hE κ D G q d h k S < upper ∧ d ∈ S' h then 1 else 0

lemma bandNonexitCost_zero_above (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) (d : α) (h : ℕ) (p₀ upper : ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S)
    (hu : upper ≤ reverseHazard M hE κ D G q d h k S) (C : Finset α) :
    reverseCost M hE κ D G n (bandNonexitCost M hE κ D G q d h p₀ upper) m k S C = 0 := by
  induction m generalizing k S with
  | zero => rfl
  | succ m ih =>
    rw [reverseCost, bandNonexitCost, ite_eq_right (fun hc => (not_lt_of_ge hu) hc.2.1)]
    have hm := reverseHazard_step_mono M hE κ D G n q hq0 hq1 d h k S closed C
    rw [ih (k-1) _ (reverseStepTree_closed M hE κ k D S G n C) (hu.trans hm)]
    exact zero_add 0

lemma bandNonexitCost_eq_count (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) (d : α) (h : ℕ) (p₀ upper : ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S)
    (hl : p₀ ≤ reverseHazard M hE κ D G q d h k S) (C : Finset α) :
    reverseCost M hE κ D G n (bandNonexitCost M hE κ D G q d h p₀ upper) m k S C =
      reverseNonexitCount M hE κ D G n
        (fun k S => upper ≤ reverseHazard M hE κ D G q d h k S) d h m k S C := by
  induction m generalizing k S with
  | zero => rfl
  | succ m ih =>
    by_cases hu : upper ≤ reverseHazard M hE κ D G q d h k S
    · rw [bandNonexitCost_zero_above M hE κ D G n q hq0 hq1 d h p₀ upper (m+1) k S closed hu C,
        reverseNonexitCount, ite_eq_left hu]
    · have hlt := lt_of_not_ge hu
      rw [reverseCost, reverseNonexitCount, ite_eq_right hu]
      simp only [bandNonexitCost, hl, hlt, true_and]
      congr 1
      exact ih (k-1) _ (reverseStepTree_closed M hE κ k D S G n C)
        (hl.trans (reverseHazard_step_mono M hE κ D G n q hq0 hq1 d h k S closed C))

theorem bandNonexitCost_budget_after_entry (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) (d : α) (h : ℕ) (p₀ upper : ℝ)
    (hp : 0 < p₀) (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S)
    (hl : p₀ ≤ reverseHazard M hE κ D G q d h k S) :
    reverseMeanCost M hE κ D G n q (bandNonexitCost M hE κ D G q d h p₀ upper) m k S ≤
      Real.log (1 / p₀) := by
  unfold reverseMeanCost
  have heq : bitsExpectation q univ
      (reverseCost M hE κ D G n (bandNonexitCost M hE κ D G q d h p₀ upper) m k S) =
      bitsExpectation q univ (reverseNonexitCount M hE κ D G n
        (fun k S => upper ≤ reverseHazard M hE κ D G q d h k S) d h m k S) := by
    apply bitsExpectation_congr
    intro C hC
    exact bandNonexitCost_eq_count M hE κ D G n q hq0 hq1 d h p₀ upper m k S closed hl C
  rw [heq]
  apply (reverse_nonexit_budget M hE κ D G n hG _ d h m k S closed q hq0 hq1 (hp.trans_le hl)).trans
  apply Real.log_le_log
  · exact one_div_pos.mpr (hp.trans_le hl)
  · exact one_div_le_one_div_of_le hp hl

end MatroidProphet

end OAI
