import OAI.Probability.MatroidProphet.Reverse.Hazard
import OAI.Probability.MatroidProphet.ExitNumerics

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

theorem bandNonexitCost_budget (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) (d : α) (h : ℕ) (p₀ upper : ℝ)
    (hp : 0 < p₀) (hp1 : p₀ ≤ 1) (m : ℕ) (k : ℤ) (S : ℕ → Set α)
    (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q (bandNonexitCost M hE κ D G q d h p₀ upper) m k S ≤
      Real.log (1 / p₀) := by
  have hlog : 0 ≤ Real.log (1 / p₀) := Real.log_nonneg ((one_le_div hp).mpr hp1)
  induction m generalizing k S with
  | zero => simpa only [reverseMeanCost_zero] using hlog
  | succ m ih =>
    by_cases hl : p₀ ≤ reverseHazard M hE κ D G q d h k S
    · exact bandNonexitCost_budget_after_entry M hE κ D G n hG q hq0 hq1 d h p₀ upper hp (m+1) k S closed hl
    · rw [reverseMeanCost_succ M hE κ D G n hG q _ m k S closed]
      calc
        _ ≤ bitsExpectation q univ (fun _ => Real.log (1 / p₀)) := by
          apply bitsExpectation_mono q hq0 hq1
          intro C hC
          simp only [bandNonexitCost, hl, false_and, ↓reduceIte, zero_add]
          exact ih (k-1) _ (reverseStepTree_closed M hE κ k D S G n C)
        _ = _ := bitsExpectation_const q univ _

noncomputable def bandExitCost (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ)
    (p₀ upper : ℝ) (k : ℤ) (S S' : ℕ → Set α) : ℝ :=
  if p₀ ≤ reverseHazard M hE κ D G q d h k S ∧
      reverseHazard M hE κ D G q d h k S < upper ∧ d ∈ S h ∧ d ∉ S' h then 1 else 0

noncomputable def bandCountCost (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ)
    (p₀ upper : ℝ) (k : ℤ) (S _ : ℕ → Set α) : ℝ :=
  if p₀ ≤ reverseHazard M hE κ D G q d h k S ∧
      reverseHazard M hE κ D G q d h k S < upper ∧ d ∈ S h then 1 else 0

lemma bandCountCost_step_split (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (d : α) (h : ℕ) (p₀ upper : ℝ) (k : ℤ) (S : ℕ → Set α)
    (closed : ReverseClosed M hE κ D k S) (C : Finset α) :
    bandCountCost M hE κ D G q d h p₀ upper k S ((reverseStepTree M hE κ k D S G n).run C) =
      bandNonexitCost M hE κ D G q d h p₀ upper k S ((reverseStepTree M hE κ k D S G n).run C) +
      bandExitCost M hE κ D G q d h p₀ upper k S ((reverseStepTree M hE κ k D S G n).run C) := by
  have hc := reverseStepTree_contracts M hE κ k D S G n closed C h
  unfold bandCountCost bandNonexitCost bandExitCost
  by_cases hS : d ∈ S h <;> by_cases hN : d ∈ (reverseStepTree M hE κ k D S G n).run C h
  · simp [hS, hN]
  · simp [hS, hN]
  · exact (hS (hc hN)).elim
  · simp [hS, hN]

lemma bandCountCost_mean_split (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (d : α) (h : ℕ) (p₀ upper : ℝ) (m : ℕ) (k : ℤ) (S : ℕ → Set α)
    (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q (bandCountCost M hE κ D G q d h p₀ upper) m k S =
      reverseMeanCost M hE κ D G n q (bandNonexitCost M hE κ D G q d h p₀ upper) m k S +
      reverseMeanCost M hE κ D G n q (bandExitCost M hE κ D G q d h p₀ upper) m k S := by
  have hpoint (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) (C : Finset α) :
      reverseCost M hE κ D G n (bandCountCost M hE κ D G q d h p₀ upper) m k S C =
        reverseCost M hE κ D G n (bandNonexitCost M hE κ D G q d h p₀ upper) m k S C +
        reverseCost M hE κ D G n (bandExitCost M hE κ D G q d h p₀ upper) m k S C := by
    induction m generalizing k S with
    | zero => simp only [reverseCost, add_zero]
    | succ m ih =>
      rw [reverseCost, reverseCost, reverseCost, bandCountCost_step_split M hE κ D G n q d h p₀ upper k S closed C,
        ih (k-1) _ (reverseStepTree_closed M hE κ k D S G n C)]
      ring
  unfold reverseMeanCost
  rw [← bitsExpectation_add]
  exact bitsExpectation_congr q univ (fun C _ => hpoint m k S closed C)

lemma bandExitCost_count_le_one (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (d : α) (h : ℕ) (p₀ upper : ℝ) (m : ℕ) (k : ℤ) (S : ℕ → Set α)
    (closed : ReverseClosed M hE κ D k S) (C : Finset α) :
    reverseCost M hE κ D G n (bandExitCost M hE κ D G q d h p₀ upper) m k S C ≤
      if d ∈ S h then 1 else 0 := by
  induction m generalizing k S with
  | zero => simp only [reverseCost]; split_ifs <;> norm_num
  | succ m ih =>
    have hi := ih (k-1) _ (reverseStepTree_closed M hE κ k D S G n C)
    have hc := reverseStepTree_contracts M hE κ k D S G n closed C h
    rw [reverseCost]
    by_cases hS : d ∈ S h <;> by_cases hN : d ∈ (reverseStepTree M hE κ k D S G n).run C h
    · simpa [bandExitCost, hS, hN] using hi
    · simp only [hN, ite_false] at hi
      have hb : bandExitCost M hE κ D G q d h p₀ upper k S ((reverseStepTree M hE κ k D S G n).run C) ≤ 1 := by
        unfold bandExitCost
        split_ifs <;> norm_num
      simpa only [hS, ite_true, add_zero] using add_le_add hb hi
    · exact (hS (hc hN)).elim
    · simpa [bandExitCost, hS, hN] using hi

lemma bandExitCost_mean_le_one (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (h : ℕ) (p₀ upper : ℝ) (m : ℕ) (k : ℤ) (S : ℕ → Set α)
    (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q (bandExitCost M hE κ D G q d h p₀ upper) m k S ≤ 1 := by
  unfold reverseMeanCost
  calc
    _ ≤ bitsExpectation q univ (fun _ => 1) := by
      apply bitsExpectation_mono q hq0 hq1
      intro C hC
      apply (bandExitCost_count_le_one M hE κ D G n q d h p₀ upper m k S closed C).trans
      split_ifs <;> norm_num
    _ = 1 := bitsExpectation_one q univ

lemma bandExitCost_le_upper_count (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (h : ℕ) (hh : h ≤ n) (p₀ upper : ℝ) (m : ℕ) (k : ℤ) (S : ℕ → Set α)
    (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q (bandExitCost M hE κ D G q d h p₀ upper) m k S ≤
      upper * reverseMeanCost M hE κ D G n q (bandCountCost M hE κ D G q d h p₀ upper) m k S := by
  rw [← reverseMeanCost_mul]
  apply reverseMeanCost_le_of_step M hE κ D G n hG q hq0 hq1
  · intro l R hR
    by_cases hb : p₀ ≤ reverseHazard M hE κ D G q d h l R ∧
        reverseHazard M hE κ D G q d h l R < upper ∧ d ∈ R h
    · have heq : bitsExpectation q univ (fun C => bandExitCost M hE κ D G q d h p₀ upper l R
          ((reverseStepTree M hE κ l D R G n).run C)) = reverseHazard M hE κ D G q d h l R := by
        rw [reverseHazard_eq_step M hE κ D G n hG q d h hh]
        apply bitsExpectation_congr
        intro C hC
        simp only [bandExitCost, hb.1, hb.2.1, hb.2.2, true_and]
      rw [heq]
      simpa only [bandCountCost, hb.1, hb.2.1, hb.2.2, true_and, ite_true, mul_one, bitsExpectation_const] using hb.2.1.le
    · have hz : ∀ C, bandExitCost M hE κ D G q d h p₀ upper l R
          ((reverseStepTree M hE κ l D R G n).run C) = 0 := by
        intro C
        unfold bandExitCost
        apply ite_eq_right
        intro hc
        exact hb ⟨hc.1, hc.2.1, hc.2.2.1⟩
      simp only [hz, bandCountCost, hb, ite_false, mul_zero, bitsExpectation_const, le_refl]
  · exact closed

theorem reverse_exit_band_bound (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (h : ℕ) (hh : h ≤ n) (p₀ upper : ℝ) (hp : 0 < p₀) (hp1 : p₀ ≤ 1) (hu : 0 ≤ upper)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q (bandExitCost M hE κ D G q d h p₀ upper) m k S ≤
      upper * (Real.log (1 / p₀) + 1) := by
  have he := bandExitCost_le_upper_count M hE κ D G n hG q hq0 hq1 d h hh p₀ upper m k S closed
  rw [bandCountCost_mean_split M hE κ D G n q d h p₀ upper m k S closed] at he
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ hu
  exact add_le_add (bandNonexitCost_budget M hE κ D G n hG q hq0 hq1 d h p₀ upper hp hp1 m k S closed)
    (bandExitCost_mean_le_one M hE κ D G n q hq0 hq1 d h p₀ upper m k S closed)

end MatroidProphet

end OAI
