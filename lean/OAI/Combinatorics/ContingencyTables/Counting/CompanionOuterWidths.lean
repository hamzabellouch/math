import OAI.Combinatorics.ContingencyTables.Counting.CompanionRestartContinuation
import OAI.Combinatorics.ContingencyTables.Rooted.RootedPhaseHistory

namespace OAI

/-! # Executed phase widths and the source history word

The supplied precision markers do not contribute to the number of oracle
bits. After identifying the computed scalar controls, the complete phase
width is the source width plus its unused padding.
-/
namespace ContingencyTables.CompanionOuterWidths
open MatchingFPRAS CompanionFactorialApplication CompanionComputedInitial
open CompanionOracleDensity GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma configs_blockWidth (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    CompanionObservationQueriesProgram.blockWidth
      (CompanionOuterPhaseProgram.configs A C K H T N R L j epsilon z v reserve)=
      CompanionPhaseWords.observationBits A C K j
        (TreeFraction.val (CountingPhaseParametersProgram.noise
          (CompanionInitializedRestartProgram.parameters A H T N R L epsilon))) := by
  unfold CompanionOuterPhaseProgram.configs
  exact CompanionObservationQueriesProgram.blockWidth_phaseConfigs A C K j _ z v _ _ _ _

lemma configs_blockWidth_reserve (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (a b : List Bool) :
    CompanionObservationQueriesProgram.blockWidth
      (CompanionOuterPhaseProgram.configs A C K H T N R L j epsilon z v a)=
      CompanionObservationQueriesProgram.blockWidth
        (CompanionOuterPhaseProgram.configs A C K H T N R L j epsilon z v b) := by
  rw [configs_blockWidth,configs_blockWidth]

def tailWidth (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) (padding : ℕ) : ℕ :=
  let p := CompanionInitializedRestartProgram.parameters A H T N R L epsilon
  let xi := TreeFraction.val (CountingPhaseParametersProgram.noise p)
  let k := CountingPhaseParametersProgram.precision p
  let obs := CountingPhaseParametersProgram.observations p
  obs*CompanionBooleanPhase.stepBits A C K j k xi+
    ((obs+1)*CompanionObservationQueriesProgram.blockWidth
      (CompanionOuterPhaseProgram.configs A C K H T N R L j epsilon z v reserve)+padding)

def phaseWidth (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) (padding : ℕ) : ℕ :=
  wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
    (CompanionRestartProgram.sumBits A C K j
      (CompanionInitializedRestartProgram.parameters A H T N R L epsilon)+
      tailWidth A C K H T N R L j epsilon z v reserve padding)

lemma phaseWidth_reserve (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (a b : List Bool) (padding : ℕ) :
    phaseWidth A C K H T N R L j epsilon z v a padding=
      phaseWidth A C K H T N R L j epsilon z v b padding := by
  unfold phaseWidth tailWidth
  rw [configs_blockWidth_reserve A C K H T N R L j epsilon z v a b]

lemma initialWidth_eq (A : Instance (Fin m) (Fin n)) (C K H N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) :
    wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
      CompanionRestartProgram.sumBits A C K j
        (CompanionInitializedRestartProgram.parameters A H
          (CompanionTargetMixing.restartTime A H L) N R L epsilon)=
      RootedRestartWords.initialStageBits A C K H L
        (CountingPhaseParametersProgram.precision
          (CompanionInitializedRestartProgram.parameters A H
            (CompanionTargetMixing.restartTime A H L) N R L epsilon))
        R (CountingPhaseSchedule.initialPrecision H) j
        (TreeFraction.val (CountingPhaseParametersProgram.noise
          (CompanionInitializedRestartProgram.parameters A H
            (CompanionTargetMixing.restartTime A H L) N R L epsilon))) := by
  rw [CompanionRestartSchedule.initialWidths_eq]
  rfl

theorem phaseWidth_source (A : Instance (Fin m) (Fin n))
    (s : RootedPhaseHistory.Settings A) (N j : ℕ) (epsilon : TreeFraction.Fraction)
    (z : View A→ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) s.K)
    (reserve : List Bool) (padding : ℕ)
    (hk : CountingPhaseParametersProgram.precision
      (CompanionInitializedRestartProgram.parameters A s.H
        (CompanionTargetMixing.restartTime A s.H s.L) N s.n s.L epsilon)=s.k)
    (hN : CountingPhaseParametersProgram.observations
      (CompanionInitializedRestartProgram.parameters A s.H
        (CompanionTargetMixing.restartTime A s.H s.L) N s.n s.L epsilon)=s.N)
    (hh : CountingPhaseSchedule.initialPrecision s.H=s.h)
    (hxi : TreeFraction.val (CountingPhaseParametersProgram.noise
      (CompanionInitializedRestartProgram.parameters A s.H
        (CompanionTargetMixing.restartTime A s.H s.L) N s.n s.L epsilon))=s.xi) :
    phaseWidth A s.C s.K s.H (CompanionTargetMixing.restartTime A s.H s.L)
      N s.n s.L j epsilon z v reserve padding=RootedPhaseHistory.width A s j+padding := by
  unfold phaseWidth tailWidth
  rw [configs_blockWidth]
  rw [←Nat.add_assoc,initialWidth_eq]
  simp only [hk,hN,hh,hxi,RootedPhaseHistory.width,CompanionPhaseWords.phaseBits,Nat.add_assoc]

end
end ContingencyTables.CompanionOuterWidths

end OAI
