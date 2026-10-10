import OAI.Probability.SATComputability.ReplacementEstimate

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped BigOperators Classical

def testKills {n k : ℕ} (U : Finset (DeletionCandidate n))
    (c : Fin k → SignedLiteral n) : Prop :=
  ∀ x ∈ U, ∀ l, literalFalse x (c l)

def batchKills {n k d : ℕ} (U : Finset (DeletionCandidate n))
    (cs : Fin d → Fin k → SignedLiteral n) : Prop :=
  ∀ x ∈ U, ∃ j, ∀ l, literalFalse x (cs j l)

noncomputable def batchKillProbability {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k d : ℕ) : ℝ :=
  (FiniteLaw.uniform : FiniteLaw (Fin d → Fin k → SignedLiteral n)).expect
    (fun cs => if batchKills U cs then 1 else 0)

theorem batchKillProbability_ge {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k d : ℕ) :
    1 - (1 - oneTestKill U k)^d ≤ batchKillProbability U k d := by
  let f : (Fin k → SignedLiteral n) → ℝ := fun c => if ¬testKills U c then 1 else 0
  have hf : (FiniteLaw.uniform : FiniteLaw (Fin k → SignedLiteral n)).expect f =
      1 - oneTestKill U k := by
    have he (c : Fin k → SignedLiteral n) :
        f c = 1 - (if testKills U c then 1 else 0) := by
      dsimp [f]
      by_cases h : testKills U c <;> simp [h]
    rw [show f = (fun c => 1 - (if testKills U c then 1 else 0)) from funext he]
    rw [FiniteLaw.expect_sub, FiniteLaw.expect_const]
    simp only [oneTestKill, testKills]
    congr 1
    apply FiniteLaw.expect_congr
    intro c
    split_ifs with h
    · exact ite_eq_left h
    · exact ite_eq_right h
  have hp : (FiniteLaw.uniform : FiniteLaw (Fin d → Fin k → SignedLiteral n)).expect
      (fun cs => ∏ j, f (cs j)) = (1 - oneTestKill U k)^d := by
    rw [uniformFiniteLaw_pi]
    calc
      _ = ∏ _ : Fin d, (FiniteLaw.uniform : FiniteLaw (Fin k → SignedLiteral n)).expect f :=
        FiniteLaw.expect_pi_product (fun _ => FiniteLaw.uniform) (fun _ => f)
      _ = _ := by simp [hf]
  have hpoint (cs : Fin d → Fin k → SignedLiteral n) :
      1 - ∏ j, f (cs j) ≤ if batchKills U cs then 1 else 0 := by
    dsimp [f]
    rw [Fintype.prod_boole]
    by_cases h : ∀ j, ¬testKills U (cs j)
    · rw [ite_eq_left h, sub_self]
      split <;> norm_num
    · obtain ⟨j, hj⟩ := not_forall.mp h
      have hj' := not_not.mp hj
      have hb : batchKills U cs := fun x hx => ⟨j, hj' x hx⟩
      rw [ite_eq_right h, ite_eq_left hb]
      norm_num
  have hmean := (FiniteLaw.uniform : FiniteLaw (Fin d → Fin k → SignedLiteral n)).expect_mono hpoint
  rw [FiniteLaw.expect_sub, FiniteLaw.expect_const, hp] at hmean
  exact hmean

theorem relaxed_one_replacement {n : ℕ} [NeZero n]
    {U : Finset (DeletionCandidate n)} (hU : U.Nonempty) {d : ℕ} (hd : 0 < d) :
    oneTestKill U 2 - 1 / (d : ℝ)^2 ≤ batchKillProbability U 3 d := by
  have hn := frozenFraction_nonneg U
  have hh := frozenFraction_le_half hU
  have hr := two_to_three_replacement hn hh hd
  have hb := batchKillProbability_ge U 3 d
  rw [oneTestKill_eq] at hb
  rw [oneTestKill_eq]
  linarith

end FixedClauseThreshold.Computability

end OAI
