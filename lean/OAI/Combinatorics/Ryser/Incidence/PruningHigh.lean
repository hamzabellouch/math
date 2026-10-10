import OAI.Combinatorics.Ryser.Incidence.PruningCore

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Incidence

variable {Pt Ln : Type*} [instDecidableEqPt : DecidableEq Pt] [instDecidableEqLn : DecidableEq Ln]

theorem high_degree_sum_le {A : Type*} (S : Finset A) (deg : A → ℕ)
    {H B : ℝ} (hH : 0 < H) (hB : (∑ a ∈ S, (deg a : ℝ) ^ 2) ≤ B) :
    (∑ a ∈ S.filter (fun a => ¬ (deg a : ℝ) ≤ H), (deg a : ℝ)) ≤ B / H := by
  classical
  apply (le_div_iff₀ hH).2
  rw [Finset.sum_mul]
  calc
    (∑ a ∈ S.filter (fun a => ¬ (deg a : ℝ) ≤ H), (deg a : ℝ) * H) ≤
        ∑ a ∈ S.filter (fun a => ¬ (deg a : ℝ) ≤ H), (deg a : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro a ha
      have hlarge := (Finset.mem_filter.mp ha).2
      have hnonneg : 0 ≤ (deg a : ℝ) := Nat.cast_nonneg _
      nlinarith [lt_of_not_ge hlarge]
    _ ≤ ∑ a ∈ S, (deg a : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by
        intro a _ _
        exact sq_nonneg _)
    _ ≤ B := hB

theorem incidenceCount_mono_left (R : Pt → Ln → Prop) {P P' : Finset Pt}
    (hP : P ⊆ P') (L : Finset Ln) : incidenceCount R P L ≤ incidenceCount R P' L := let _ := instDecidableEqPt; let _ := instDecidableEqLn; by
  apply Finset.sum_le_sum_of_subset_of_nonneg hP
  intro p _ _
  exact Nat.zero_le _

theorem incidenceCount_mono_right (R : Pt → Ln → Prop) (P : Finset Pt)
    {L L' : Finset Ln} (hL : L ⊆ L') : incidenceCount R P L ≤ incidenceCount R P L' := by
  apply Finset.sum_le_sum
  intro p _
  exact leftDegree_mono R hL p

theorem high_degree_truncation (R : Pt → Ln → Prop) (P : Finset Pt) (L : Finset Ln)
    {H BP BL : ℝ} (hH : 0 < H)
    (hBP : (∑ p ∈ P, (leftDegree R L p : ℝ) ^ 2) ≤ BP)
    (hBL : (∑ l ∈ L, (rightDegree R P l : ℝ) ^ 2) ≤ BL) :
    let P₀ := P.filter (fun p => (leftDegree R L p : ℝ) ≤ H)
    let L₀ := L.filter (fun l => (rightDegree R P l : ℝ) ≤ H)
    (incidenceCount R P L : ℝ) - BP / H - BL / H ≤ (incidenceCount R P₀ L₀ : ℝ) := by
  classical
  dsimp only
  let P₀ := P.filter (fun p => (leftDegree R L p : ℝ) ≤ H)
  let L₀ := L.filter (fun l => (rightDegree R P l : ℝ) ≤ H)
  let Pbad := P.filter (fun p => ¬ (leftDegree R L p : ℝ) ≤ H)
  let Lbad := L.filter (fun l => ¬ (rightDegree R P l : ℝ) ≤ H)
  have hleft : (incidenceCount R P₀ L : ℝ) +
      (∑ p ∈ Pbad, (leftDegree R L p : ℝ)) = (incidenceCount R P L : ℝ) := by
    simpa only [P₀, Pbad, incidenceCount, Nat.cast_sum] using
      Finset.sum_filter_add_sum_filter_not P
        (fun p => (leftDegree R L p : ℝ) ≤ H) (fun p => (leftDegree R L p : ℝ))
  have hright : (incidenceCount R P₀ L₀ : ℝ) +
      (∑ l ∈ Lbad, (rightDegree R P₀ l : ℝ)) = (incidenceCount R P₀ L : ℝ) := by
    rw [incidenceCount_swap R P₀ L₀, incidenceCount_swap R P₀ L]
    simpa only [L₀, Lbad, incidenceCount, rightDegree, Nat.cast_sum] using
      Finset.sum_filter_add_sum_filter_not L
        (fun l => (rightDegree R P l : ℝ) ≤ H) (fun l => (rightDegree R P₀ l : ℝ))
  have hbadP : (∑ p ∈ Pbad, (leftDegree R L p : ℝ)) ≤ BP / H :=
    high_degree_sum_le P (leftDegree R L) hH hBP
  have hbadL : (∑ l ∈ Lbad, (rightDegree R P₀ l : ℝ)) ≤ BL / H := by
    calc
      _ ≤ ∑ l ∈ Lbad, (rightDegree R P l : ℝ) := by
        apply Finset.sum_le_sum
        intro l _
        exact_mod_cast rightDegree_mono R (Finset.filter_subset _ _) l
      _ ≤ BL / H := high_degree_sum_le L (rightDegree R P) hH hBL
  change (incidenceCount R P L : ℝ) - BP / H - BL / H ≤
    (incidenceCount R P₀ L₀ : ℝ)
  linarith

theorem exists_pruned_core (R : Pt → Ln → Prop) (P : Finset Pt) (L : Finset Ln)
    {d H BP BL : ℝ} (hd : 0 ≤ d) (hH : 0 < H)
    (hBP : (∑ p ∈ P, (leftDegree R L p : ℝ) ^ 2) ≤ BP)
    (hBL : (∑ l ∈ L, (rightDegree R P l : ℝ) ^ 2) ≤ BL) :
    ∃ P' : Finset Pt, P' ⊆ P ∧ ∃ L' : Finset Ln, L' ⊆ L ∧
      MinimumDegrees R d P' L' ∧
      (∀ p ∈ P', (leftDegree R L' p : ℝ) ≤ H) ∧
      (∀ l ∈ L', (rightDegree R P' l : ℝ) ≤ H) ∧
      (incidenceCount R P L : ℝ) - BP / H - BL / H -
        d * ((P.card : ℝ) + (L.card : ℝ)) ≤ (incidenceCount R P' L' : ℝ) := by
  classical
  let P₀ := P.filter (fun p => (leftDegree R L p : ℝ) ≤ H)
  let L₀ := L.filter (fun l => (rightDegree R P l : ℝ) ≤ H)
  have hP₀ : P₀ ⊆ P := Finset.filter_subset _ _
  have hL₀ : L₀ ⊆ L := Finset.filter_subset _ _
  obtain ⟨P', hP', L', hL', hmin, hpot⟩ := exists_degree_core R d P₀ L₀
  refine ⟨P', hP'.trans hP₀, L', hL'.trans hL₀, hmin, ?_, ?_, ?_⟩
  · intro p hp
    have hdeg := (Finset.mem_filter.mp (hP' hp)).2
    have hmono : (leftDegree R L' p : ℝ) ≤ (leftDegree R L p : ℝ) := by
      exact_mod_cast leftDegree_mono R (hL'.trans hL₀) p
    exact hmono.trans hdeg
  · intro l hl
    have hdeg := (Finset.mem_filter.mp (hL' hl)).2
    have hmono : (rightDegree R P' l : ℝ) ≤ (rightDegree R P l : ℝ) := by
      exact_mod_cast rightDegree_mono R (hP'.trans hP₀) l
    exact hmono.trans hdeg
  · have hhigh := high_degree_truncation R P L hH hBP hBL
    change (incidenceCount R P L : ℝ) - BP / H - BL / H ≤
      (incidenceCount R P₀ L₀ : ℝ) at hhigh
    have hlow := degree_core_incidence_lower_bound R hd P₀ P' L₀ L' hpot
    have hcardP : (P₀.card : ℝ) ≤ (P.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hP₀
    have hcardL : (L₀.card : ℝ) ≤ (L.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hL₀
    have hcharge := mul_le_mul_of_nonneg_left (add_le_add hcardP hcardL) hd
    linarith

end RyserCoveringCounterexample.Incidence

end

end OAI
