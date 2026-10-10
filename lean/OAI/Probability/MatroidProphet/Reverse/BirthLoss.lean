import OAI.Probability.MatroidProphet.Reverse.SquareSum

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

lemma pathExitSquare_nonneg (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h m : ℕ) (C : Finset α) :
    0 ≤ pathExitSquare M hE κ D G q d h m C := by
  unfold pathExitSquare
  split_ifs
  · exact sq_nonneg _
  · exact le_rfl

lemma pathExitSquare_eq_doubleExit (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (h : ℕ) (d : α) (m : ℕ) :
    bitsExpectation q univ (pathExitSquare M hE κ D G q d h m) =
      bitsExpectation q univ (fun C => bitsExpectation q univ
        (reverseDoubleExit M hE κ D ((reversePrefixTree M hE κ D G h m (-1) (fun _ => Set.univ)).run C)
          G (-(m:ℤ)-1) h d C)) := by
  rw [reverseDoubleExit_after_prefix M hE κ D G h d hG q m (-1) _ (reverseClosed_univ M hE κ D (-1))]
  apply bitsExpectation_congr
  intro C hC
  have hp (j : ℕ) (hj : j ≤ h) := reversePrefixTree_from_univ_path M hE κ D G h hG m C hj
  rw [hp h le_rfl, reverseHazard_state_congr M hE κ D _ _ G q _ h d (fun j hj => hp j hj.le)]
  rfl

omit [DecidableEq α] in
lemma doubleExit_le_birth (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (C T : Finset α) (b : ℤ) (h : ℕ)
    (d : α) (hd : d ∉ M.closure ∅)
    (hS : ∀ j ≤ h, S j = nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j b) :
    reverseDoubleExit M hE κ D S G (b-1) h d C T ≤
      if nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d = b then 1 else 0 := by
  unfold reverseDoubleExit
  by_cases hs : d ∈ S h
  · rw [ite_eq_left hs]
    by_cases hn : d ∉ reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S (b-1) h
    · rw [ite_eq_left hn, one_mul]
      have hbirth : nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d = b := by
        rw [hS h le_rfl, mem_nominal_iff_birth_le M hE κ D _ h d hd b] at hs
        rw [reverseNominal_actual_state M hE κ D S G C b h hS,
          mem_nominal_iff_birth_le M hE κ D _ h d hd (b-1)] at hn
        omega
      rw [ite_eq_left hbirth]
      split_ifs <;> norm_num
    · simp only [ite_eq_right hn, zero_mul]
      split_ifs <;> norm_num
  · simp only [ite_eq_right hs]
    split_ifs <;> norm_num

theorem pathExitSquare_le_birth_probability (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (h : ℕ) (d : α) (hd : d ∉ M.closure ∅) (m : ℕ) :
    bitsExpectation q univ (pathExitSquare M hE κ D G q d h m) ≤
      bitsExpectation q univ (fun C =>
        if nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d = -(m:ℤ) then 1 else 0) := by
  rw [pathExitSquare_eq_doubleExit M hE κ D G hG q h d m]
  apply bitsExpectation_mono q hq0 hq1
  intro C hC
  rw [← bitsExpectation_const q univ (if nominalBirth M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h d = -(m:ℤ) then 1 else 0)]
  apply bitsExpectation_mono q hq0 hq1
  intro T hT
  exact doubleExit_le_birth M hE κ D _ G C T (-(m:ℤ)) h d hd
    (fun j hj => reversePrefixTree_from_univ_path M hE κ D G h hG m C hj)

omit [DecidableEq α] in
lemma nominalBirth_baseline_iff (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (d : α) (hd : d ∉ M.closure ∅) :
    nominalBirth M hE κ D C h d = activation h ↔ d ∈ densityExpansion M hE κ (D h) (M.closure ∅) := by
  have hm := mem_nominal_iff_birth_le M hE κ D C h d hd (activation h)
  rw [nominalPath_baseline] at hm
  have hb := (nominalBirth_bounds M hE κ D C h d).1
  exact ⟨fun he => hm.mpr he.le, fun he => le_antisymm (hm.mp he) hb⟩

end MatroidProphet

end OAI
