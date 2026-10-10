import OAI.Combinatorics.ContingencyTables.Counting.InitialMultiplierValues
import OAI.Combinatorics.ContingencyTables.Counting.CompanionMultiplierUpdate

namespace OAI

/-!
# Actual companion phase history and counting-error composition

Each stored multiplier is the explicit initial rational value followed by
the actual empirical plain/defect update. Successful finite observations
propagate goodness and add at most 4 eta to the logarithmic counting error.
-/

namespace ContingencyTables.CompanionPhaseComposition

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication CompanionAnnealing CompanionInitialization
open CompanionMultiplierUpdate TwoLiftStates

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def weights (A : Instance I J) (samples : ℕ → List (Set (Labels A×Bool))) :
    ℕ → ((Labels A×Bool)×(Labels A×Bool)) → ((Labels A×Bool)×(Labels A×Bool)) → ℝ
  | 0 => CompanionInitialMultipliers.multiplier A
  | j+1 => learnedMultipliers pairs (weights A samples j) (samples j)

def Accurate (A : Instance I J) (samples : ℕ → List (Set (Labels A×Bool))) (eta : ℝ) (j : ℕ) : Prop :=
  AccuratePhase pairs (weights A samples j) (weight A j) (ratio A j) eta (samples j)

/-- Goodness is obtained for the actual stored phase multipliers from
exact initialization and every preceding successful observation. -/
theorem weights_good (A : Instance I J) (samples : ℕ → List (Set (Labels A×Bool)))
    (eta : ℝ) (he0 : 0≤ eta) (he : eta≤1/4) (L : ℕ)
    (hall : ∀ j< L,Accurate A samples eta j) :
    GoodMultipliers pairs (weight A L) (weights A samples L) := by
  induction L with
  | zero =>
    simpa only [weights,weight,Nat.cast_zero,zero_div] using CompanionInitialMultipliers.initial_good A
  | succ L ih =>
    have hg := ih (by intro j hj; exact hall j (by omega))
    exact successful_phase_learns A L (weights A samples L) hg.positive eta he0 he
      (samples L) (hall L (by omega))

noncomputable def observedRatio (A : Instance I J) (samples : ℕ → List (Set (Labels A×Bool))) (j : ℕ) : ℝ :=
  empiricalRatio pairs (ratio A j) (samples j)

noncomputable def total (A : Instance I J) (j : ℕ) : ℝ := slotTotal pairs (weight A j) ∅

lemma total_positive (A : Instance I J) (j : ℕ) : 0< total A j :=
  slotTotal_pos pairs _ (weight_positive A j) ∅ PairedLabels.fresh

lemma observedRatio_positive (A : Instance I J) (samples : ℕ → List (Set (Labels A×Bool)))
    (eta : ℝ) (he : eta≤1/4) (j : ℕ)
    (hw : ∀ p r,0< weights A samples j p r) (hacc : Accurate A samples eta j) :
    0< observedRatio A samples j := by
  have hZ := chainTotal_pos pairs PairedLabels.fresh PairedLabels.cover (weights A samples j)
    (weight A j) (weight_positive A j) hw
  have hp : 0< chainMean pairs (weights A samples j) (weight A j) (plainObservable pairs (ratio A j)) := by
    rw [ratio_mean]
    exact div_pos (total_positive A (j+1)) hZ
  have hq : 0< chainMean pairs (weights A samples j) (weight A j) (plainObservable pairs (fun _ => 1)) := by
    rw [plain_probability_mean pairs PairedLabels.fresh PairedLabels.cover]
    exact div_pos (total_positive A j) hZ
  have hph := relative_error_bounds _ _ _ (hacc (.inr ()))
  simp only [phaseObservable] at hph
  have hqh := accurate_plain pairs (weights A samples j) (weight A j) (ratio A j) eta (samples j) hacc
  exact div_pos (AnnealingMultipliers.empirical_positive hp he hph.1)
    (AnnealingMultipliers.empirical_positive hq he hqh.1)

noncomputable def estimate (A : Instance I J) (samples : ℕ → List (Set (Labels A×Bool))) : ℕ → ℝ
  | 0 => total A 0
  | j+1 => estimate A samples j*observedRatio A samples j

/-- The actual product estimator has total logarithmic error at most
4 L eta on the event that every preceding phase observation is accurate. -/
theorem estimate_log_error (A : Instance I J) (samples : ℕ → List (Set (Labels A×Bool)))
    (eta : ℝ) (he0 : 0≤ eta) (he : eta≤1/4) (L : ℕ)
    (hall : ∀ j< L,Accurate A samples eta j) :
    0< estimate A samples L ∧
      |Real.log (estimate A samples L/total A L)|≤4*(L:ℝ)*eta := by
  induction L with
  | zero =>
    have hT := total_positive A 0
    exact ⟨hT,by simp [estimate,div_self hT.ne']⟩
  | succ L ih =>
    have hprev : ∀ j< L,Accurate A samples eta j := by intro j hj; exact hall j (by omega)
    have hE := ih hprev
    have hg := weights_good A samples eta he0 he L hprev
    have hR := observedRatio_positive A samples eta he L hg.positive (hall L (by omega))
    have hstep := successful_phase_ratio_log A L (weights A samples L) hg.positive eta he0 he
      (samples L) (hall L (by omega))
    change |Real.log (observedRatio A samples L/(total A (L+1)/total A L))|≤4*eta at hstep
    have hT := total_positive A L
    have hT' := total_positive A (L+1)
    have hid : estimate A samples (L+1)/total A (L+1)=
        (estimate A samples L/total A L)*(observedRatio A samples L/(total A (L+1)/total A L)) := by
      change (estimate A samples L*observedRatio A samples L)/total A (L+1)=_
      field_simp [hT.ne',hT'.ne']
    refine ⟨mul_pos hE.1 hR,?_⟩
    rw [hid,Real.log_mul (div_ne_zero hE.1.ne' hT.ne')
      (div_ne_zero hR.ne' (div_ne_zero hT'.ne' hT.ne'))]
    have hsum := abs_add_le (Real.log (estimate A samples L/total A L))
      (Real.log (observedRatio A samples L/(total A (L+1)/total A L)))
    push_cast
    linarith [hE.2,hstep]

end ContingencyTables.CompanionPhaseComposition

end OAI
