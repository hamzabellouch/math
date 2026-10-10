import OAI.Combinatorics.ContingencyTables.Rooted.RootedPhaseTrial
import OAI.Combinatorics.ContingencyTables.Rooted.RootedTerminalApplication

namespace OAI

/-! # Soundness of the actual stored rational count estimate -/

namespace ContingencyTables.RootedStoredEstimate

open CommonBasesFPRAS CompanionFactorialApplication CompanionRationalUpdates
open CompanionPhaseWords (Stored)
open RootedWarmStart RootedPhaseTrial
open CompanionReferenceAccuracy (relative_of_log_error)
open CompanionTerminalMass (Endpoints tableCount tableCount_ge_one)
open CompanionTerminalApplication (finalPhase)
open TwoLiftStates
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

def initialTotal (A : Instance I J) : ℚ :=
  (∏ a : ForestAssignmentSplit.FreeCell A.small A.T,((A.b a.val.1 a.val.2+1:ℕ):ℚ))*
    ∏ s : SmallCell A,((A.b s.val.1 s.val.2+1:ℕ):ℚ)

def initialStored (A : Instance I J) : Stored A :=
  ⟨initial A,initialTotal A⟩

lemma initialTotal_cast (A : Instance I J) (R : RootedCompletion.Selection A.T) :
    (initialTotal A:ℝ)=total A R 0 := by
  rw [total,total_zero]
  simp only [initialTotal,CompanionInitialization.freeTotal,Rat.cast_mul,Rat.cast_prod,
    Rat.cast_add,Rat.cast_natCast,Rat.cast_one,Nat.cast_add,Nat.cast_one]

lemma initialStored_positive (A : Instance I J) (R : RootedCompletion.Selection A.T) :
    (∀ p q,0 < (initialStored A).multiplier p q) ∧ 0 < (initialStored A).estimate := by
  constructor
  · exact initial_positive A
  · have h : (0:ℝ) < (initialTotal A:ℝ) := by
      rw [initialTotal_cast A R]
      exact total_positive A R 0
    exact_mod_cast h

lemma initialStored_good (A : Instance I J) (R : RootedCompletion.Selection A.T) :
    GoodMultipliers pairs (RootedAnnealing.weight A R 0)
      (fun p q => ((initialStored A).multiplier p q:ℝ)) := by
  have hw : (fun p q => ((initialStored A).multiplier p q:ℝ))=
      CompanionInitialMultipliers.multiplier A := by
    funext p q
    exact initial_cast A p q
  rw [hw,zero_weight_eq]
  simpa only [CompanionAnnealing.weight,Nat.cast_zero,zero_div] using
    CompanionInitialMultipliers.initial_good A

/-- The actual rational estimates telescope through their proved
per-phase multiplicative errors, including every weight-oracle error. -/
theorem stored_log_error (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (stored : ℕ → Stored A) (hinit : stored 0=initialStored A)
    (xi : ℚ) (eta : ℝ) (H : ℕ)
    (hstep : ∀ j,j < H → ValidOutput A R j (stored j) xi eta (stored (j+1))) :
    0 < (stored H).estimate ∧
      |Real.log (((stored H).estimate:ℝ)/total A R H)| ≤
        (H:ℝ)*(4*(xi:ℝ)+4*eta) := by
  induction H with
  | zero =>
    rw [hinit]
    refine ⟨(initialStored_positive A R).2,?_⟩
    have he : ((initialStored A).estimate:ℝ)=total A R 0 := initialTotal_cast A R
    rw [he,div_self (total_positive A R 0).ne']
    simp
  | succ H ih =>
    have hprev := ih (fun j hj => hstep j (by omega))
    have hnext := hstep H (by omega)
    have hold : (0:ℝ) < ((stored H).estimate:ℝ) := by exact_mod_cast hprev.1
    have hnew : (0:ℝ) < ((stored (H+1)).estimate:ℝ) := by exact_mod_cast hnext.2.1
    have hT := total_positive A R H
    have hT' := total_positive A R (H+1)
    have heq : ((stored (H+1)).estimate:ℝ)/total A R (H+1)=
        (((stored H).estimate:ℝ)/total A R H)*
          (((stored (H+1)).estimate:ℝ)/
            (((stored H).estimate:ℝ)*(total A R (H+1)/total A R H))) := by
      field_simp [hold.ne',hT.ne',hT'.ne']
    refine ⟨hnext.2.1,?_⟩
    rw [heq,Real.log_mul (div_ne_zero hold.ne' hT.ne')
      (div_ne_zero hnew.ne' (mul_ne_zero hold.ne' (div_ne_zero hT'.ne' hT.ne')))]
    have hb := abs_add_le
      (Real.log (((stored H).estimate:ℝ)/total A R H))
      (Real.log (((stored (H+1)).estimate:ℝ)/
        (((stored H).estimate:ℝ)*(total A R (H+1)/total A R H))))
    have hs : |Real.log (((stored (H+1)).estimate:ℝ)/
        (((stored H).estimate:ℝ)*(total A R (H+1)/total A R H)))| ≤
        4*(xi:ℝ)+4*eta := hnext.2.2.2
    push_cast
    nlinarith [hprev.2]

theorem stored_count_accuracy (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (E : Endpoints A) (L : ℕ) (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (hW : 20*A.d ≤ A.W) (hL : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^L)
    (stored : ℕ → Stored A) (hinit : stored 0=initialStored A)
    (xi : ℚ) (eta : ℝ)
    (herr : (finalPhase A L epsilon:ℝ)*(4*(xi:ℝ)+4*eta) ≤ epsilon/50)
    (hstep : ∀ j,j < finalPhase A L epsilon →
      ValidOutput A R j (stored j) xi eta (stored (j+1))) :
    (1-epsilon)*tableCount A ≤ ((stored (finalPhase A L epsilon)).estimate:ℝ) ∧
      ((stored (finalPhase A L epsilon)).estimate:ℝ) ≤ (1+epsilon)*tableCount A := by
  have hs := stored_log_error A R stored hinit xi eta (finalPhase A L epsilon) hstep
  have hZ := total_positive A R (finalPhase A L epsilon)
  have hratio := relative_of_log_error epsilon
    (((stored (finalPhase A L epsilon)).estimate:ℝ)/total A R (finalPhase A L epsilon))
    he0 he1 (div_pos (by exact_mod_cast hs.1) hZ) (hs.2.trans herr)
  have hb : (1-epsilon/4)*total A R (finalPhase A L epsilon) ≤
        ((stored (finalPhase A L epsilon)).estimate:ℝ) ∧
      ((stored (finalPhase A L epsilon)).estimate:ℝ) ≤
        (1+epsilon/4)*total A R (finalPhase A L epsilon) :=
    ⟨(le_div_iff₀ hZ).mp hratio.1,(div_le_iff₀ hZ).mp hratio.2⟩
  apply final_estimate_accuracy epsilon (tableCount A) (total A R (finalPhase A L epsilon))
    ((stored (finalPhase A L epsilon)).estimate:ℝ) he0 he1 (by linarith [tableCount_ge_one A])
  · have ht := RootedTerminalApplication.terminal_normalizer A R E L epsilon he0 he1 hW hL
    refine ⟨ht.1,ht.2.trans ?_⟩
    nlinarith [tableCount_ge_one A]
  · exact hb

end
end ContingencyTables.RootedStoredEstimate

end OAI
