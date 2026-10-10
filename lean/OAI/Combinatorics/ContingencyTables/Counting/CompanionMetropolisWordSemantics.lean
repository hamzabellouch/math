import OAI.Combinatorics.ContingencyTables.Counting.CompanionMetropolisWordProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionMetropolisLaw
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordSlices

namespace OAI

/-! # The flat physical transition has the proved phase-step law -/

namespace ContingencyTables.CompanionMetropolisWordProgram

open MatchingFPRAS CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionOracleDensity CompanionWeightOracle
open CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram CommonBasesFPRAS
open CompanionBooleanPhase (State)
open FiniteObservableTransport TwoLiftStates GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

def packed (frame : CompanionMetropolisProgram.Frame) (k : ℕ) (code : List ℕ) (bits : List Bool) : Input :=
  (((frame,k),code),bits)

lemma fields_ofFn (frame : CompanionMetropolisProgram.Frame) (k p q : ℕ) (code : List ℕ)
    (bits : Fin (1+(p+((q+q)+k))) → Bool)
    (hp : proposalWidth (packed frame k code (List.ofFn bits))=p)
    (hq : queryWidth (packed frame k code (List.ofFn bits))=q) :
    fields (packed frame k code (List.ofFn bits))=
      ((FiniteWordSlices.split p q k bits).1 0,
        (List.ofFn (FiniteWordSlices.split p q k bits).2.1,
          ((List.ofFn (FiniteWordSlices.split p q k bits).2.2.1.1,
            List.ofFn (FiniteWordSlices.split p q k bits).2.2.1.2),
            List.ofFn (FiniteWordSlices.split p q k bits).2.2.2))) := by
  let inp := packed frame k code (List.ofFn bits)
  change ((List.ofFn bits).getD 0 false,
    (((List.ofFn bits).drop 1).take (proposalWidth inp),
      ((((List.ofFn bits).drop (1+proposalWidth inp)).take (queryWidth inp),
        ((List.ofFn bits).drop (1+proposalWidth inp+queryWidth inp)).take (queryWidth inp)),
        ((List.ofFn bits).drop (1+proposalWidth inp+queryWidth inp+queryWidth inp)).take k)))=_
  change proposalWidth inp=p at hp
  change queryWidth inp=q at hq
  rw [hp,hq,FiniteWordSlices.holding_bit,FiniteWordSlices.first_slice,
    FiniteWordSlices.current_slice,FiniteWordSlices.target_slice,FiniteWordSlices.coin_slice]

lemma proposalWidth_code (A : Instance (Fin m) (Fin n))
    (frame : CompanionMetropolisProgram.Frame) (k : ℕ) (S : Set (Labels A × Bool)) (bits : List Bool) :
    proposalWidth (packed frame k (encodeSet (coordinateOrder A) S) bits)=
      CompanionBooleanPhase.proposalBits A := by
  have hc := Fintype.card_congr (coordinateOrder A)
  simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fin] at hc
  have hd : (CanonicalInitialEncoding.pairOrder (capacities A)).length/2=Fintype.card (Labels A) := by omega
  simp only [proposalWidth,packed,encodeSet,List.length_ofFn,hd,CompanionBooleanPhase.proposalBits]

lemma queryWidth_config (A : Instance (Fin m) (Fin n)) (C K j k : ℕ) (xi : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) (w : FractionMatrix) (code : List ℕ) (bits : List Bool) :
    queryWidth (packed (RootedLabelWeightProgram.config A C K j xi xi z v degree depth,w) k code bits)=
      medianEstimatorBits A C K j xi xi := by
  exact CompanionEvaluatedWeightProgram.queryWidth A C K j xi z v

lemma output_ofFn (A : Instance (Fin m) (Fin n)) (C K j k : ℕ) (xi : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (S : State A) (bits : Fin (CompanionBooleanPhase.stepBits A C K j k xi) → Bool) :
    output (packed (RootedLabelWeightProgram.config A C K j xi xi z v degree depth,matrixCode w)
      k (encodeSet (coordinateOrder A) S.val) (List.ofFn bits))=
      CompanionMetropolisProgram.output (CompanionMetropolisProgram.programInput A C K j k xi
        (RootedLabelWeightProgram.config A C K j xi xi z v degree depth) w S
        (CompanionBooleanPhase.stepWordEquiv A C K j k xi bits)) := by
  have hf := fields_ofFn
    (RootedLabelWeightProgram.config A C K j xi xi z v degree depth,matrixCode w) k
    (CompanionBooleanPhase.proposalBits A) (medianEstimatorBits A C K j xi xi)
    (encodeSet (coordinateOrder A) S.val) bits
    (proposalWidth_code A _ k S.val _) (queryWidth_config A C K j k xi z v degree depth _ _ _)
  have hi : stepInput (packed
      (RootedLabelWeightProgram.config A C K j xi xi z v degree depth,matrixCode w)
      k (encodeSet (coordinateOrder A) S.val) (List.ofFn bits))=
      CompanionMetropolisProgram.programInput A C K j k xi
        (RootedLabelWeightProgram.config A C K j xi xi z v degree depth) w S
        (CompanionBooleanPhase.stepWordEquiv A C K j k xi bits) := by
    exact congrArg (fun fs =>
      (((RootedLabelWeightProgram.config A C K j xi xi z v degree depth,matrixCode w),
        encodeSet (coordinateOrder A) S.val),fs)) hf
  exact congrArg CompanionMetropolisProgram.output hi

/-- The actual polynomial flat-step implementation has exactly the
reference kernel used by the trajectory and return estimates. -/
theorem sameLaw_flat (A : Instance (Fin m) (Fin n)) (C K j k : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (xi : ℚ) (hxi : 0 < xi) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S : State A) :
    SameLaw (fun bits : Fin (CompanionBooleanPhase.stepBits A C K j k xi) → Bool =>
      output (packed (RootedLabelWeightProgram.config A C K j xi xi z v degree depth,matrixCode w)
        k (encodeSet (coordinateOrder A) S.val) (List.ofFn bits)))
      (fun bits => encodeSet (coordinateOrder A)
        (RootedBooleanPhase.step A (RootedCompletion.rowColumn A.T) C K j k hK hW xi
          (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w) S bits).val) := by
  let f := fun b : CompanionMetropolisProgram.Fields A C K j k xi =>
    CompanionMetropolisProgram.output (CompanionMetropolisProgram.programInput A C K j k xi
      (RootedLabelWeightProgram.config A C K j xi xi z v degree depth) w S b)
  let g := fun b : CompanionMetropolisProgram.Fields A C K j k xi =>
    encodeSet (coordinateOrder A)
      (RootedBooleanPhase.step A (RootedCompletion.rowColumn A.T) C K j k hK hW xi
        (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w) S
          ((CompanionBooleanPhase.stepWordEquiv A C K j k xi).symm b)).val
  have hfg : SameLaw f g := CompanionMetropolisProgram.sameLaw_fields A C K j k hC hj hK hW hB
    xi hxi z v degree depth hdegree hdepth w S
  intro phi
  simp_rw [output_ofFn]
  have hf := uniformAverage_equiv (CompanionBooleanPhase.stepWordEquiv A C K j k xi)
    (fun b => phi (f b))
  have hg := uniformAverage_equiv (CompanionBooleanPhase.stepWordEquiv A C K j k xi)
    (fun b => phi (g b))
  refine hf.trans ((hfg phi).trans ?_)
  simpa only [g,Equiv.symm_apply_apply] using hg.symm

end
end ContingencyTables.CompanionMetropolisWordProgram

end OAI
