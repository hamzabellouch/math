import OAI.Combinatorics.ContingencyTables.Transport.FiniteRecordedHistory
import OAI.Combinatorics.ContingencyTables.Counting.CompanionFlatReturnProgram
import OAI.Combinatorics.ContingencyTables.Rooted.RootedCappedReturn

namespace OAI

/-! # The executed return scan has the reference capped-return law -/

namespace ContingencyTables.RootedReturnHistoryLaw

open MatchingFPRAS CommonBasesFPRAS FirstSuccess ResidualMixture FiniteObservableTransport
open RealKernelApproximation
open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle
open CompanionRationalUpdates CompanionCappedReturn CompanionPhaseTrajectory
open CompanionComputedInitial CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram
open TwoLiftStates GridBoundary
open scoped Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

theorem trace_return_sameLaw (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K j k n : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S : PlainIndex (pairs : List (Pair A))) :
    SameLaw (fun words : Fin (n+1) → (Fin (CompanionBooleanPhase.stepBits A C K j k xi) → Bool) =>
      returnDefault (plainPredicate pairs) S (traceStates
        (RootedBooleanPhase.step A R C K j k hK hW xi v w) S.val (List.ofFn words)))
      (RootedCappedReturn.returnWordDefault A R C K j k n hK hW xi v w S) := by
  let F := RootedBooleanPhase.step A R C K j k hK hW xi v w
  let ret := fun a : PathState (CompanionBooleanPhase.State A) (n+1) =>
    returnDefault (plainPredicate pairs) S (historyPrefix a)
  have hb := RootedBooleanPhase.recordedWalk_law A R C K j k (n+1) (n+1) hK hW xi v w S.val
  have ha := RootedArithmeticStep.recordedWalk_law A R C K j k (n+1) (n+1) hK hW xi v w S.val
  have hp := SameLaw.of_mapLaw_eq
    (RootedBooleanPhase.recordedWalk A R C K j k (n+1) (n+1) hK hW xi v w S.val)
    (RootedArithmeticStep.recordedWalk A R C K j k (n+1) (n+1) hK hW xi v w S.val)
    (hb.trans ha.symm)
  have hm := hp.map ret
  have hprefix (bits : Fin ((n+1)*CompanionBooleanPhase.stepBits A C K j k xi) → Bool) :
      historyPrefix (RootedBooleanPhase.recordedWalk A R C K j k (n+1) (n+1) hK hW xi v w S.val bits)=
      traceStates F S.val (List.ofFn (gridWordEquiv (n+1)
        (CompanionBooleanPhase.stepBits A C K j k xi) bits)) :=
    recorded_prefix F (n+1) S.val (n+1) le_rfl _
  intro phi
  have he := uniformAverage_equiv (gridWordEquiv (n+1) (CompanionBooleanPhase.stepBits A C K j k xi))
    (fun words => phi (returnDefault (plainPredicate pairs) S (traceStates F S.val (List.ofFn words))))
  have ht : uniformAverage (fun bits => phi (ret
      (RootedBooleanPhase.recordedWalk A R C K j k (n+1) (n+1) hK hW xi v w S.val bits)))=
      uniformAverage (fun words : Fin (n+1) → (Fin (CompanionBooleanPhase.stepBits A C K j k xi) → Bool) =>
        phi (returnDefault (plainPredicate pairs) S (traceStates F S.val (List.ofFn words)))) := by
    calc
      _ = uniformAverage (fun bits => phi (returnDefault (plainPredicate pairs) S
          (traceStates F S.val (List.ofFn (gridWordEquiv (n+1)
            (CompanionBooleanPhase.stepBits A C K j k xi) bits))))) := by
        apply congrArg uniformAverage
        funext bits
        exact congrArg (fun xs => phi (returnDefault (plainPredicate pairs) S xs)) (hprefix bits)
      _ = _ := he
  refine ht.symm.trans ((hm phi).trans ?_)
  rfl

variable {m n : ℕ}

/-- The physical flat-return program can replace the literal reference
return in every subsequent restart or adaptive phase experiment. -/
theorem flatReturn_sameLaw (A : Instance (Fin m) (Fin n)) (C K j k cap : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (xi : ℚ) (hxi : 0 < xi) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (S : PlainIndex (pairs : List (Pair A))) :
    SameLaw (fun bits : Fin ((cap+1)*CompanionBooleanPhase.stepBits A C K j k xi) → Bool =>
      CompanionFlatReturnProgram.output (CompanionFlatReturnProgram.data A C K j k (cap+1)
        xi z v degree depth w S.val (List.ofFn bits)))
      (fun bits => CompanionArithmeticProposal.encodeSet (coordinateOrder A)
        (RootedCappedReturn.returnWordDefault A (RootedCompletion.rowColumn A.T) C K j k cap
          hK hW xi (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w) S bits).val.val) := by
  have h₁ := CompanionFlatReturnProgram.output_sameLaw A C K j k (cap+1) hC hj hK hW hB xi hxi
    z v degree depth hdegree hdepth w S
  have h₂ := (trace_return_sameLaw A (RootedCompletion.rowColumn A.T) C K j k cap hK hW xi
    (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w) S).map
      (fun T => CompanionArithmeticProposal.encodeSet (coordinateOrder A) T.val.val)
  intro phi
  exact (h₁ phi).trans (h₂ phi)

end
end ContingencyTables.RootedReturnHistoryLaw

end OAI
