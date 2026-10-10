import OAI.Probability.SATComputability.DeletionHistory

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped Classical

theorem encode_deletedVariables {n : ℕ} (x : DeletionCandidate n) :
    encodeDeletion (deletedVariables x) (fun v => (x v).getD false) = x := by
  funext v
  cases hx : x v <;> simp [encodeDeletion, deletedVariables, hx]

noncomputable def minimumDeletions {n : ℕ} (U : Finset (DeletionCandidate n)) : ℕ :=
  if h : U.Nonempty then U.inf' h (fun x => (deletedVariables x).card) else n+1

theorem minimumDeletions_le_iff {n r : ℕ} {U : Finset (DeletionCandidate n)}
    (hU : U.Nonempty) : minimumDeletions U ≤ r ↔
      ∃ x ∈ U, (deletedVariables x).card ≤ r := by
  rw [minimumDeletions, dite_eq_left hU]
  exact Finset.inf'_le_iff hU

theorem DeletionHistory.best_nonneg {n M r : ℕ} (H : DeletionHistory n M) :
    0 ≤ bestDeletionTime H.realStop r := by
  have h0 : (0 : ℝ) ≤ H.realStop ∅ := Nat.cast_nonneg _
  apply h0.trans
  exact Finset.le_sup' _ (by simp [allowedDeletions])

theorem DeletionHistory.minimumDeletions_lower {n M t r : ℕ}
    (H : DeletionHistory n M) (ht : 0 < t) (hr : r ≤ n) :
    (r : ℝ) * (1 - bestDeletionTime H.realStop r / t) ≤
      minimumDeletions (H.state t) := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hfrac : 0 ≤ bestDeletionTime H.realStop r / t :=
    div_nonneg H.best_nonneg ht0.le
  have hmul : (r : ℝ) * (1 - bestDeletionTime H.realStop r / t) ≤ r := by
    nlinarith [show (0 : ℝ) ≤ r from Nat.cast_nonneg r]
  by_cases hU : (H.state t).Nonempty
  · by_cases hmin : minimumDeletions (H.state t) ≤ r
    · obtain ⟨x, hx, hxr⟩ := (minimumDeletions_le_iff hU).mp hmin
      have hs : candidateSurvives (H.state t) (deletedVariables x) :=
        ⟨fun v => (x v).getD false, by simpa only [encode_deletedVariables] using hx⟩
      have htime := H.survival_le_best hxr hs
      have hratio : 1 ≤ bestDeletionTime H.realStop r / t :=
        (le_div_iff₀ ht0).mpr (by simpa using htime.le)
      have hnonpos : (r : ℝ) * (1 - bestDeletionTime H.realStop r / t) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg r) (by linarith)
      exact hnonpos.trans (Nat.cast_nonneg _)
    · have hm : (r : ℝ) ≤ minimumDeletions (H.state t) := by
        exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hmin))
      exact hmul.trans hm
  · rw [minimumDeletions, dite_eq_right hU]
    exact hmul.trans (by exact_mod_cast (hr.trans (Nat.le_succ n)))

theorem mean_minimumDeletions_lower {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    {n M t r : ℕ} (H : Ω → DeletionHistory n M) (ht : 0 < t) (hr : r ≤ n) :
    (r : ℝ) * (1 - P.expect (fun ω => bestDeletionTime (H ω).realStop r) / t) ≤
      P.expect (fun ω => (minimumDeletions ((H ω).state t) : ℝ)) := by
  have h := P.expect_mono (fun ω => (H ω).minimumDeletions_lower ht hr)
  simpa only [FiniteLaw.expect_mul_left, FiniteLaw.expect_sub,
    FiniteLaw.expect_const, FiniteLaw.expect_div] using h

end FixedClauseThreshold.Computability

end OAI
