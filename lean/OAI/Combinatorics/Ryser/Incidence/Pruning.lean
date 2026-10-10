import OAI.Combinatorics.Ryser.Incidence.PruningHigh
import OAI.Combinatorics.Ryser.Incidence.DegreeSquares
import OAI.Combinatorics.Ryser.Incidence.AllLineCap
import OAI.Combinatorics.Ryser.Incidence.PruningNumerics

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Incidence

variable {Pt Ln : Type*} [instDecidableEqPt : DecidableEq Pt] [instDecidableEqLn : DecidableEq Ln]

theorem incidenceCount_le_card_mul (R : Pt → Ln → Prop) (P : Finset Pt)
    (L : Finset Ln) : incidenceCount R P L ≤ P.card * L.card := let _ := instDecidableEqPt; let _ := instDecidableEqLn; by
  calc
    incidenceCount R P L ≤ ∑ p ∈ P, L.card := by
      apply Finset.sum_le_sum
      intro p _
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = P.card * L.card := by simp

theorem incidenceCount_le_card_mul_max (R : Pt → Ln → Prop) (P : Finset Pt)
    (L : Finset Ln) {H : ℝ} (hmax : ∀ p ∈ P, (leftDegree R L p : ℝ) ≤ H) :
    (incidenceCount R P L : ℝ) ≤ (P.card : ℝ) * H := let _ := instDecidableEqPt; let _ := instDecidableEqLn; by
  calc
    (incidenceCount R P L : ℝ) = ∑ p ∈ P, (leftDegree R L p : ℝ) := by
      simp only [incidenceCount, Nat.cast_sum]
    _ ≤ ∑ p ∈ P, H := Finset.sum_le_sum hmax
    _ = (P.card : ℝ) * H := by simp

variable {F : Type*} [Field F] [DecidableEq F]

theorem exists_projective_pruning_sqrt (P : Finset (ProjectivePoint F))
    (L : Finset (ProjectiveLine F)) {U q : ℝ} (hU : 2 ≤ U) (hq : 0 < q)
    (hd : 2 ≤ lowerDegreeCutoff U q)
    (hP : (P.card : ℝ) ≤ U * q) (hL : (L.card : ℝ) ≤ U * q)
    (hI : q * Real.sqrt q / U ≤ (incidenceCount ProjectiveIncidence P L : ℝ)) :
    ∃ P' : Finset (ProjectivePoint F), P' ⊆ P ∧
      ∃ L' : Finset (ProjectiveLine F), L' ⊆ L ∧
        q * Real.sqrt q / (2 * U) ≤ (incidenceCount ProjectiveIncidence P' L' : ℝ) ∧
        q / (32 * U ^ 4) ≤ (P'.card : ℝ) ∧
        q / (32 * U ^ 4) ≤ (L'.card : ℝ) ∧
        (P'.card : ℝ) ≤ U * q ∧ (L'.card : ℝ) ≤ U * q ∧
        MinimumDegrees ProjectiveIncidence (lowerDegreeCutoff U q) P' L' ∧
        (∀ p ∈ P', (leftDegree ProjectiveIncidence L' p : ℝ) ≤ upperDegreeCutoff U q) ∧
        (∀ l ∈ L', (rightDegree ProjectiveIncidence P' l : ℝ) ≤ upperDegreeCutoff U q) ∧
        (∀ l : ProjectiveLine F,
          (rightDegree ProjectiveIncidence P' l : ℝ) ≤ upperDegreeCutoff U q) := by
  classical
  have hUpos : 0 < U := lt_of_lt_of_le (by norm_num) hU
  have hUq : 0 ≤ U * q := mul_nonneg hUpos.le hq.le
  have hIcard : (incidenceCount ProjectiveIncidence P L : ℝ) ≤
      (P.card : ℝ) * (L.card : ℝ) := by
    exact_mod_cast incidenceCount_le_card_mul ProjectiveIncidence P L
  have hprod : (P.card : ℝ) * (L.card : ℝ) ≤ (U * q) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hP hL (Nat.cast_nonneg _) hUq
  have hPsq : (P.card : ℝ) ^ 2 ≤ (U * q) ^ 2 :=
    (sq_le_sq₀ (Nat.cast_nonneg _) hUq).2 hP
  have hLsq : (L.card : ℝ) ^ 2 ≤ (U * q) ^ 2 :=
    (sq_le_sq₀ (Nat.cast_nonneg _) hUq).2 hL
  have hBP : (∑ p ∈ P, (leftDegree ProjectiveIncidence L p : ℝ) ^ 2) ≤
      2 * U ^ 2 * q ^ 2 := by
    have hs := sum_projective_leftDegree_sq_le P L
    nlinarith
  have hBL : (∑ l ∈ L, (rightDegree ProjectiveIncidence P l : ℝ) ^ 2) ≤
      2 * U ^ 2 * q ^ 2 := by
    have hs := sum_projective_rightDegree_sq_le P L
    nlinarith
  have hHpos := upperDegreeCutoff_pos hUpos hq
  have hdpos := lowerDegreeCutoff_pos hUpos hq
  obtain ⟨P', hP', L', hL', hmin, hmaxP, hmaxL, hloss⟩ :=
    exists_pruned_core ProjectiveIncidence P L hdpos.le hHpos hBP hBL
  have hPbound : (P'.card : ℝ) ≤ U * q := by
    have hsub : (P'.card : ℝ) ≤ (P.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hP'
    exact hsub.trans hP
  have hLbound : (L'.card : ℝ) ≤ U * q := by
    have hsub : (L'.card : ℝ) ≤ (L.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hL'
    exact hsub.trans hL
  have hIbound : q * Real.sqrt q / (2 * U) ≤
      (incidenceCount ProjectiveIncidence P' L' : ℝ) := by
    have hcharge := mul_le_mul_of_nonneg_left (add_le_add hP hL) hdpos.le
    have hbudget := pruning_budget_exact hUpos hq
    linarith
  have hPcard : q / (32 * U ^ 4) ≤ (P'.card : ℝ) := by
    rw [← pruned_card_ratio hUpos hq]
    apply (div_le_iff₀ hHpos).2
    exact hIbound.trans (incidenceCount_le_card_mul_max ProjectiveIncidence P' L' hmaxP)
  have hLcard : q / (32 * U ^ 4) ≤ (L'.card : ℝ) := by
    rw [← pruned_card_ratio hUpos hq]
    apply (div_le_iff₀ hHpos).2
    have hswap : (incidenceCount ProjectiveIncidence P' L' : ℝ) =
        (incidenceCount (fun l p => ProjectiveIncidence p l) L' P' : ℝ) := by
      rw [incidenceCount_swap]
    rw [hswap] at hIbound
    exact hIbound.trans (incidenceCount_le_card_mul_max
      (fun l p => ProjectiveIncidence p l) L' P' hmaxL)
  refine ⟨P', hP', L', hL', hIbound, hPcard, hLcard, hPbound, hLbound,
    hmin, hmaxP, hmaxL, ?_⟩
  intro l
  exact (projective_all_line_cap P' L' (by linarith) hmin.1 l).trans
    (all_line_cap_numeric hUpos hq hd hLbound)

theorem exists_projective_pruning (P : Finset (ProjectivePoint F))
    (L : Finset (ProjectiveLine F)) {U q r : ℝ} (hU : 2 ≤ U) (hq : 0 < q)
    (hsq : r ^ 2 = q) (hr : 16 * U ^ 2 ≤ r)
    (hP : (P.card : ℝ) ≤ U * q) (hL : (L.card : ℝ) ≤ U * q)
    (hI : q * r / U ≤ (incidenceCount ProjectiveIncidence P L : ℝ)) :
    ∃ P' : Finset (ProjectivePoint F), P' ⊆ P ∧
      ∃ L' : Finset (ProjectiveLine F), L' ⊆ L ∧
        q * r / (2 * U) ≤ (incidenceCount ProjectiveIncidence P' L' : ℝ) ∧
        q / (32 * U ^ 4) ≤ (P'.card : ℝ) ∧
        q / (32 * U ^ 4) ≤ (L'.card : ℝ) ∧
        (P'.card : ℝ) ≤ U * q ∧ (L'.card : ℝ) ≤ U * q ∧
        MinimumDegrees ProjectiveIncidence (r / (8 * U ^ 2)) P' L' ∧
        (∀ p ∈ P', (leftDegree ProjectiveIncidence L' p : ℝ) ≤ 16 * U ^ 3 * r) ∧
        (∀ l ∈ L', (rightDegree ProjectiveIncidence P' l : ℝ) ≤ 16 * U ^ 3 * r) ∧
        (∀ l : ProjectiveLine F, (rightDegree ProjectiveIncidence P' l : ℝ) ≤
          16 * U ^ 3 * r) := by
  have hUpos : 0 < U := lt_of_lt_of_le (by norm_num) hU
  have hrnonneg : 0 ≤ r := (mul_nonneg (by norm_num) (sq_nonneg U)).trans hr
  have hsqrt : Real.sqrt q = r := (Real.sqrt_eq_iff_eq_sq hq.le hrnonneg).2 hsq.symm
  have hd : 2 ≤ lowerDegreeCutoff U q := by
    unfold lowerDegreeCutoff
    rw [hsqrt]
    apply (le_div_iff₀ (mul_pos (by norm_num) (pow_pos hUpos 2))).2
    nlinarith
  have hI' : q * Real.sqrt q / U ≤ (incidenceCount ProjectiveIncidence P L : ℝ) := by
    simpa only [hsqrt] using hI
  simpa only [lowerDegreeCutoff, upperDegreeCutoff, hsqrt] using
    exists_projective_pruning_sqrt P L hU hq hd hP hL hI'

end RyserCoveringCounterexample.Incidence

end

end OAI
