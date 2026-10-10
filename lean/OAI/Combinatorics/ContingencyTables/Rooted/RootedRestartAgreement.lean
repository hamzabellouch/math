import OAI.Combinatorics.ContingencyTables.Counting.CompanionMultiplierAgreement
import OAI.Combinatorics.ContingencyTables.Rooted.RootedRestartWords
import OAI.Combinatorics.ContingencyTables.Rooted.RootedPhaseExperiment

namespace OAI

/-! # Restart histories depend only on stored canonical pair entries -/
namespace ContingencyTables.FirstSuccess
open scoped Classical
noncomputable section

theorem varyingWalk_congr_prefix {X : Type*} [Fintype X] [DecidableEq X]
    (width : ℕ → ℕ)
    (f g : (i : ℕ) → X → (Fin (width i) → Bool) → X)
    (x : X) (n : ℕ) (h : ∀ i,i < n → f i=g i)
    (bits : VaryingWords width n) :
    varyingWalk width f x n bits=varyingWalk width g x n bits := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [varyingWalk]
    rw [ih (fun i hi => h i (by omega)) (Fin.init bits),h n (by omega)]

end
end ContingencyTables.FirstSuccess

namespace ContingencyTables.CompanionMultiplierAgreement
open CompanionFactorialApplication CompanionRationalUpdates CompanionOracleDensity
open CompanionBooleanPhase (State stepBits)
open TwoLiftStates GridBoundary
noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

theorem observedStates_eq (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K j k N : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w w' : Pair A → Pair A → ℚ)
    (hw : Agree A w w') :
    RootedPhaseExperiment.observedStates A R C K j k N hK hW xi v w=
      RootedPhaseExperiment.observedStates A R C K j k N hK hW xi v w' := by
  funext S bits i
  unfold RootedPhaseExperiment.observedStates
  rw [recordedWalk_eq A R C K j k N N hK hW xi v w w' hw]

end
end ContingencyTables.CompanionMultiplierAgreement

namespace ContingencyTables.RootedRestartWords
open CommonBasesFPRAS CompanionFactorialApplication CompanionRationalUpdates
open CompanionOracleDensity CompanionWeightOracle TwoLiftStates GridBoundary FirstSuccess
open scoped BigOperators Classical
noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

theorem stages_agree (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K H L k cap j : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K)
    (w w' : ℕ → Pair A → Pair A → ℚ)
    (hw : ∀ i,i < j → CompanionMultiplierAgreement.Agree A (w (i+1)) (w' (i+1)))
    (S : PlainIndex (pairs : List (Pair A)))
    (bits : Fin (∑ i : Fin j,stageWidth A C K H L k cap xi i.val) → Bool) :
    stages A R C K H L k cap j hK hW xi v w S bits=
      stages A R C K H L k cap j hK hW xi v w' S bits := by
  unfold stages
  apply varyingWalk_congr_prefix
  intro i hi
  exact CompanionMultiplierAgreement.returns_eq A R C K (i+1) k cap
    (CompanionTargetMixing.restartTime A H L) hK hW xi v (w (i+1)) (w' (i+1)) (hw i hi)

theorem initializedStages_agree (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K H L k cap h j : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K)
    (w w' : ℕ → Pair A → Pair A → ℚ)
    (hw : ∀ i,i < j → CompanionMultiplierAgreement.Agree A (w (i+1)) (w' (i+1)))
    (bits : Fin (initialStageBits A C K H L k cap h j xi) → Bool) :
    initializedStages A R C K H L k cap h j hK hW xi v w bits=
      initializedStages A R C K H L k cap h j hK hW xi v w' bits := by
  unfold initializedStages
  exact stages_agree A R C K H L k cap j hK hW xi v w w' hw _ _

end
end ContingencyTables.RootedRestartWords

end OAI
