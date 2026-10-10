import OAI.Combinatorics.ContingencyTables.Rooted.RootedEstimatorWordSemantics
import OAI.Combinatorics.ContingencyTables.Counting.CompanionEstimatorWords
import OAI.Combinatorics.ContingencyTables.Rooted.RootedEstimatorWords

namespace OAI

/-! # Exact finite-word law of the executed selected-root weight oracle -/

namespace ContingencyTables.RootedEstimatorWordProgram

open MatchingFPRAS CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity RootedEstimatorLayoutProgram CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

def scheduledContext (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (delta failure : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) : Context :=
  RootedEstimatorLayoutProgram.data A C K j (sampleCount j delta failure)
    (oracleTime A C K 1 delta) (oracleTime A C K 1 (correctionTheta delta))
    (offsetAccuracy A delta) z v

def scheduledEquiv (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (delta failure : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    (Fin (wordWidth (scheduledContext A C K j delta failure z v)) → Bool) ≃
      RootedComputedEstimator.Inputs A C K j delta failure :=
  (wordEquiv (scheduledContext A C K j delta failure z v)).trans
    (recodeBanks
      (ratioWidth_data A C K j _ _ _ _ z v)
      (correctionWalkWidth_data A C K j _ _ _ _ z v)
      (binWidth_data A C K j _ _ _ _ z v))

lemma scheduledWordWidth (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (delta failure : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    wordWidth (scheduledContext A C K j delta failure z v)=
      estimatorWordBits A C K j delta failure := by
  change j*(sampleCount j delta failure*ratioWidth
    (scheduledContext A C K j delta failure z v))+
    sampleCount j delta failure*(correctionWalkWidth
      (scheduledContext A C K j delta failure z v)+
        RootedEstimatorLayoutProgram.binWidth (scheduledContext A C K j delta failure z v))=_
  simp only [scheduledContext,ratioWidth_data,correctionWalkWidth_data,binWidth_data,
    RootedBinDrawLaw.wordBits_eq,estimatorWordBits,oracleIntegerBits]

private lemma oracleTime_positive (A : Instance (Fin m) (Fin n)) (C K : ℕ)
    (hC : 0 < C) (hK : 1 ≤ K) (theta : ℝ) (htheta : 0 < theta) :
    0 < oracleTime A C K 1 theta := by
  have hd : (0:ℝ) < A.d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one A.hd)
  have hk : (0:ℝ) < K := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK)
  have hh := height_positive A C (by exact_mod_cast hC)
  have hm : 0 < mixingConstant A K := by unfold mixingConstant; positivity
  have hp : 0 < mixingConstant A K*(height A C+A.d*K+16*1/theta+2) := by positivity
  have hn := Nat.le_ceil (mixingConstant A K*(height A C+A.d*K+16*1/theta+2))
  have hc : (0:ℝ) < oracleTime A C K 1 theta := by
    simpa only [oracleTime,Nat.cast_one] using hp.trans_le hn
  exact_mod_cast hc

theorem scheduledWidth_positive (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hK : 1 ≤ K) (delta failure : ℚ) (hd : 0 < delta) (hf : 0 < failure)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    0 < wordWidth (scheduledContext A C K j delta failure z v) := by
  have hdelta : (0:ℝ) < delta := by exact_mod_cast hd
  have htime := oracleTime_positive A C K hC hK (correctionTheta delta)
    (by unfold correctionTheta; positivity)
  have hstep := RootedOracleWalkProgram.stepWidth_pos A C hC
  have hs := sampleCount_positive j delta failure hd hf
  have ht : 0 < correctionWalkWidth (scheduledContext A C K j delta failure z v) := by
    rw [scheduledContext,correctionWalkWidth_data]
    exact Nat.mul_pos htime hstep
  have hc : 0 < correctionWidth (scheduledContext A C K j delta failure z v) := by
    unfold correctionWidth
    omega
  have hp := Nat.mul_pos hs hc
  change 0 < _ + sampleCount j delta failure*
    correctionWidth (scheduledContext A C K j delta failure z v)
  omega

/-- Parsing the one flat word produces precisely the sample inputs
used in the independent estimator experiment. -/
theorem prepare_scheduled (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hK : 1 ≤ K) (delta failure : ℚ) (hd : 0 < delta) (hf : 0 < failure)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool)
    (bits : Fin (wordWidth (scheduledContext A C K j delta failure z v)) → Bool) :
    prepare (input (scheduledContext A C K j delta failure z v) (degree,depth) bits)=
      RootedEstimatorExecution.data A C K j delta failure z v degree depth
        (scheduledEquiv A C K j delta failure z v bits) := by
  have hdelta : (0:ℝ) < delta := by exact_mod_cast hd
  have hstep := RootedOracleWalkProgram.stepWidth_pos A C hC
  have hrtime := oracleTime_positive A C K hC hK delta hdelta
  have hctime := oracleTime_positive A C K hC hK (correctionTheta delta)
    (by unfold correctionTheta; positivity)
  have hs : 0 < (scheduledContext A C K j delta failure z v).2.1.2 :=
    sampleCount_positive j delta failure hd hf
  have hr : 0 < ratioWidth (scheduledContext A C K j delta failure z v) := by
    rw [scheduledContext,ratioWidth_data]
    exact Nat.mul_pos hrtime hstep
  have ht : 0 < correctionWidth (scheduledContext A C K j delta failure z v) := by
    unfold correctionWidth
    have ht : 0 < correctionWalkWidth (scheduledContext A C K j delta failure z v) := by
      rw [scheduledContext,correctionWalkWidth_data]
      exact Nat.mul_pos hctime hstep
    omega
  rw [prepare_input _ _ hs hr ht]
  unfold bankInput
  have hc := encodeBanks_recode (ratioWidth_data A C K j _ _ _ _ z v)
    (correctionWalkWidth_data A C K j _ _ _ _ z v)
    (binWidth_data A C K j _ _ _ _ z v)
    (scheduledContext A C K j delta failure z v).1
    (scheduledContext A C K j delta failure z v).2.2.2
    (RootedEstimatorLayoutProgram.assignmentCount (scheduledContext A C K j delta failure z v))
    (degree,depth) (wordEquiv (scheduledContext A C K j delta failure z v) bits)
  refine hc.symm.trans ?_
  change encodeBanks (RootedOracleWalkProgram.data A C 0 K z v) j
    (offsetAccuracy A delta) (RootedEstimatorLayoutProgram.assignmentCount
      (scheduledContext A C K j delta failure z v)) (degree,depth)
        (scheduledEquiv A C K j delta failure z v bits)=_
  have hcount : RootedEstimatorLayoutProgram.assignmentCount
      (scheduledContext A C K j delta failure z v)=CompanionOracleDensity.assignmentCount A :=
    assignmentCount_data A C K j _ _ _ _ z v
  rw [hcount]
  unfold encodeBanks RootedEstimatorExecution.data RootedEstimatorExecution.ratioBlock
    RootedEstimatorExecution.correctionBlock RootedCorrectionSampleProgram.data
  simp only [phase_data]

theorem output_scheduled (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (delta failure : ℚ) (hd : 0 < delta) (hf : 0 < failure)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance delta))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance delta))
    (bits : Fin (wordWidth (scheduledContext A C K j delta failure z v)) → Bool) :
    TreeFraction.val (output (input (scheduledContext A C K j delta failure z v)
      (degree,depth) bits))=RootedComputedEstimator.estimate A C K j hK hW delta failure z v
        (scheduledEquiv A C K j delta failure z v bits) := by
  rw [output,prepare_scheduled A C K j hC hK delta failure hd hf z v degree depth bits]
  exact RootedEstimatorExecution.output_data A C K j hC hj hK hW hB delta failure z hz v
    degree depth hdegree hdepth _

theorem sameLaw_estimateValue (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (delta failure : ℚ) (hd : 0 < delta) (hf : 0 < failure)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance delta))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance delta)) :
    FiniteObservableTransport.SameLaw
      (fun bits => TreeFraction.val (output (input
        (scheduledContext A C K j delta failure z v) (degree,depth) bits)))
      (RootedOracleDensity.estimateValue A (RootedCompletion.rowColumn A.T) C z K hK hW j
        delta failure (RootedCatalogGrid.gridEquiv A K v)) := by
  intro phi
  let test := fun draws : RootedComputedEstimator.Inputs A C K j delta failure =>
    phi (RootedComputedEstimator.estimate A C K j hK hW delta failure z v draws)
  have hp := output_scheduled A C K j hC hj hK hW hB delta failure hd hf z hz v
    degree depth hdegree hdepth
  have he := uniformAverage_equiv (scheduledEquiv A C K j delta failure z v) test
  have ho : uniformAverage (fun bits => phi (TreeFraction.val (output (input
      (scheduledContext A C K j delta failure z v) (degree,depth) bits))))=
      uniformAverage (fun bits => test (scheduledEquiv A C K j delta failure z v bits)) := by
    apply congrArg uniformAverage
    funext bits
    exact congrArg phi (hp bits)
  exact ho.trans (he.trans (RootedComputedEstimator.sameLaw A C K j hC hj hK hW hB
    delta failure z hz v phi))

theorem sameLaw_word (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (epsilon failure : ℚ) (he : 0 < epsilon) (hf : 0 < failure)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance epsilon j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance epsilon j))) :
    FiniteObservableTransport.SameLaw
      (fun bits => TreeFraction.val (output (input
        (scheduledContext A C K j (innerTolerance epsilon j) failure z v) (degree,depth) bits)))
      (RootedOracleDensity.wordEstimate A (RootedCompletion.rowColumn A.T) C z K hK hW j
        epsilon failure (RootedCatalogGrid.gridEquiv A K v)) := by
  intro phi
  have hs := sameLaw_estimateValue A C K j hC hj hK hW hB (innerTolerance epsilon j)
    failure (innerTolerance_pos epsilon j he) hf z hz v degree depth hdegree hdepth phi
  have he := uniformAverage_equiv (estimatorWordEquiv A C K j (innerTolerance epsilon j) failure)
    (fun draws => phi (RootedOracleDensity.estimateValue A (RootedCompletion.rowColumn A.T)
      C z K hK hW j (innerTolerance epsilon j) failure (RootedCatalogGrid.gridEquiv A K v) draws))
  exact hs.trans he.symm

theorem output_range (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (delta failure : ℚ) (hd : 0 < delta) (hd1 : delta < 1) (hf : 0 < failure)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance delta))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance delta))
    (bits : Fin (wordWidth (scheduledContext A C K j delta failure z v)) → Bool) :
    (CompanionOracleDensity.assignmentCount A:ℝ)*(1/2:ℝ)^j/16 ≤
      (TreeFraction.val (output (input (scheduledContext A C K j delta failure z v)
        (degree,depth) bits)):ℝ) ∧
      (TreeFraction.val (output (input (scheduledContext A C K j delta failure z v)
        (degree,depth) bits)):ℝ) ≤ 8*CompanionOracleDensity.assignmentCount A := by
  rw [output,prepare_scheduled A C K j hC hK delta failure hd hf z v degree depth bits]
  exact RootedEstimatorExecution.output_range A C K j hC hj hK hW hB delta failure hd hd1 hf
    z hz v degree depth hdegree hdepth _

/-- The actual polynomial list program, on its prescribed finite word,
inherits the proved relative-error bound of the complete weight oracle. -/
theorem output_failure (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (epsilon failure : ℚ) (he0 : 0 < epsilon) (he1 : epsilon < 1) (hf : 0 < failure)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance epsilon j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance epsilon j)))
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K)) :
    uniformAverage (fun bits : Fin (wordWidth
      (scheduledContext A C K j (innerTolerance epsilon j) failure z v)) → Bool =>
      if (TreeFraction.val (output (input
          (scheduledContext A C K j (innerTolerance epsilon j) failure z v) (degree,depth) bits)):ℝ) <
          (1-(epsilon:ℝ))*RootedCountIdentification.h A (RootedCompletion.rowColumn A.T)
            ((j:ℝ)*C/height A C) z ∨
        (1+(epsilon:ℝ))*RootedCountIdentification.h A (RootedCompletion.rowColumn A.T)
            ((j:ℝ)*C/height A C) z <
          (TreeFraction.val (output (input
            (scheduledContext A C K j (innerTolerance epsilon j) failure z v) (degree,depth) bits)):ℝ)
      then (1:ℝ) else 0) ≤ (failure:ℝ)/4 := by
  let test := fun draws : RootedComputedEstimator.Inputs A C K j (innerTolerance epsilon j) failure =>
    if (TreeFraction.val (RootedEstimatorBlockProgram.output
        (RootedEstimatorExecution.data A C K j (innerTolerance epsilon j) failure z v
          degree depth draws)):ℝ) <
        (1-(epsilon:ℝ))*RootedCountIdentification.h A (RootedCompletion.rowColumn A.T)
          ((j:ℝ)*C/height A C) z ∨
      (1+(epsilon:ℝ))*RootedCountIdentification.h A (RootedCompletion.rowColumn A.T)
          ((j:ℝ)*C/height A C) z <
        (TreeFraction.val (RootedEstimatorBlockProgram.output
          (RootedEstimatorExecution.data A C K j (innerTolerance epsilon j) failure z v
            degree depth draws)):ℝ) then (1:ℝ) else 0
  have he := uniformAverage_equiv
    (scheduledEquiv A C K j (innerTolerance epsilon j) failure z v) test
  have hp := prepare_scheduled A C K j hC hK (innerTolerance epsilon j) failure
    (innerTolerance_pos epsilon j he0) hf z v degree depth
  simp only [output]
  simp_rw [hp]
  exact he.trans_le (RootedEstimatorExecution.output_failure A C K j hC hj hK hW hB
    epsilon failure he0 he1 hf z hz v degree depth hdegree hdepth hPL hCheeger)

end
end ContingencyTables.RootedEstimatorWordProgram

end OAI
