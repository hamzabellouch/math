import OAI.Combinatorics.ContingencyTables.Counting.InitialMultiplierValues
import OAI.Combinatorics.ContingencyTables.Rooted.RootedMultiplierUpdate
import OAI.Combinatorics.ContingencyTables.Rooted.RootedWarmStart
import OAI.Combinatorics.ContingencyTables.Counting.CompanionPhaseComposition

namespace OAI

/-!
# Actual companion phase history and counting-error composition

Each stored multiplier is the explicit initial rational value followed by
the actual empirical plain/defect update. Successful finite observations
propagate goodness and add at most 4 eta to the logarithmic counting error.
-/

namespace ContingencyTables.RootedPhaseComposition

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication RootedAnnealing
open RootedMultiplierUpdate TwoLiftStates
open RootedWarmStart (total total_positive)
open CompanionPhaseComposition (weights)

variable {I J : Type*} [Fintype I] [Fintype J]

def Accurate (A : Instance I J) (R : RootedCompletion.Selection A.T) (samples : ℕ → List (Set (Labels A×Bool))) (eta : ℝ) (j : ℕ) : Prop :=
  AccuratePhase pairs (weights A samples j) (weight A R j) (ratio A R j) eta (samples j)

/-- Goodness is obtained for the actual stored phase multipliers from
exact initialization and every preceding successful observation. -/
theorem weights_good (A : Instance I J) (R : RootedCompletion.Selection A.T) (samples : ℕ → List (Set (Labels A×Bool)))
    (eta : ℝ) (he0 : 0≤ eta) (he : eta≤1/4) (L : ℕ)
    (hall : ∀ j< L,Accurate A R samples eta j) :
    GoodMultipliers pairs (weight A R L) (weights A samples L) := by
  induction L with
  | zero =>
    rw [weights,RootedWarmStart.zero_weight_eq]
    simpa only [CompanionAnnealing.weight,Nat.cast_zero,zero_div] using
      CompanionInitialMultipliers.initial_good A
  | succ L ih =>
    have hg := ih (by intro j hj; exact hall j (by omega))
    exact successful_phase_learns A R L (weights A samples L) hg.positive eta he0 he
      (samples L) (hall L (by omega))

noncomputable def observedRatio (A : Instance I J) (R : RootedCompletion.Selection A.T) (samples : ℕ → List (Set (Labels A×Bool))) (j : ℕ) : ℝ :=
  empiricalRatio pairs (ratio A R j) (samples j)

lemma observedRatio_positive (A : Instance I J) (R : RootedCompletion.Selection A.T) (samples : ℕ → List (Set (Labels A×Bool)))
    (eta : ℝ) (he : eta≤1/4) (j : ℕ)
    (hw : ∀ p r,0< weights A samples j p r) (hacc : Accurate A R samples eta j) :
    0< observedRatio A R samples j := by
  have hZ := chainTotal_pos pairs PairedLabels.fresh PairedLabels.cover (weights A samples j)
    (weight A R j) (weight_positive A R j) hw
  have hp : 0< chainMean pairs (weights A samples j) (weight A R j) (plainObservable pairs (ratio A R j)) := by
    rw [ratio_mean]
    exact div_pos (total_positive A R (j+1)) hZ
  have hq : 0< chainMean pairs (weights A samples j) (weight A R j) (plainObservable pairs (fun _ => 1)) := by
    rw [plain_probability_mean pairs PairedLabels.fresh PairedLabels.cover]
    exact div_pos (total_positive A R j) hZ
  have hph := relative_error_bounds _ _ _ (hacc (.inr ()))
  simp only [phaseObservable] at hph
  have hqh := accurate_plain pairs (weights A samples j) (weight A R j) (ratio A R j) eta (samples j) hacc
  exact div_pos (AnnealingMultipliers.empirical_positive hp he hph.1)
    (AnnealingMultipliers.empirical_positive hq he hqh.1)

noncomputable def estimate (A : Instance I J) (R : RootedCompletion.Selection A.T) (samples : ℕ → List (Set (Labels A×Bool))) : ℕ → ℝ
  | 0 => total A R 0
  | j+1 => estimate A R samples j*observedRatio A R samples j

/-- The actual product estimator has total logarithmic error at most
4 L eta on the event that every preceding phase observation is accurate. -/
theorem estimate_log_error (A : Instance I J) (R : RootedCompletion.Selection A.T) (samples : ℕ → List (Set (Labels A×Bool)))
    (eta : ℝ) (he0 : 0≤ eta) (he : eta≤1/4) (L : ℕ)
    (hall : ∀ j< L,Accurate A R samples eta j) :
    0< estimate A R samples L ∧
      |Real.log (estimate A R samples L/total A R L)|≤4*(L:ℝ)*eta := by
  induction L with
  | zero =>
    have hT := total_positive A R 0
    exact ⟨hT,by simp [estimate,div_self hT.ne']⟩
  | succ L ih =>
    have hprev : ∀ j< L,Accurate A R samples eta j := by intro j hj; exact hall j (by omega)
    have hE := ih hprev
    have hg := weights_good A R samples eta he0 he L hprev
    have hR := observedRatio_positive A R samples eta he L hg.positive (hall L (by omega))
    have hstep := successful_phase_ratio_log A R L (weights A samples L) hg.positive eta he0 he
      (samples L) (hall L (by omega))
    change |Real.log (observedRatio A R samples L/(total A R (L+1)/total A R L))|≤4*eta at hstep
    have hT := total_positive A R L
    have hT' := total_positive A R (L+1)
    have hid : estimate A R samples (L+1)/total A R (L+1)=
        (estimate A R samples L/total A R L)*(observedRatio A R samples L/(total A R (L+1)/total A R L)) := by
      change (estimate A R samples L*observedRatio A R samples L)/total A R (L+1)=_
      field_simp [hT.ne',hT'.ne']
    refine ⟨mul_pos hE.1 hR,?_⟩
    rw [hid,Real.log_mul (div_ne_zero hE.1.ne' hT.ne')
      (div_ne_zero hR.ne' (div_ne_zero hT'.ne' hT.ne'))]
    have hsum := abs_add_le (Real.log (estimate A R samples L/total A R L))
      (Real.log (observedRatio A R samples L/(total A R (L+1)/total A R L)))
    push_cast
    linarith [hE.2,hstep]

end ContingencyTables.RootedPhaseComposition

end OAI
