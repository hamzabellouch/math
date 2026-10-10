import OAI.Combinatorics.ContingencyTables.Rooted.RootedEstimatorMedianProgram
import OAI.Combinatorics.ContingencyTables.Rooted.RootedEstimatorAmplification

namespace OAI

/-! # The executed inner median is the analysed amplified weight oracle -/

namespace ContingencyTables.RootedEstimatorMedianProgram

open MatchingFPRAS CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity RootedEstimatorLayoutProgram CommonBasesFPRAS
open FiniteObservableTransport
open scoped Classical

noncomputable section
variable {m n : ℕ}

def context (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (epsilon : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) : Context :=
  RootedEstimatorWordProgram.scheduledContext A C K j (innerTolerance (epsilon/2) j) 1 z v

def value (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (epsilon delta : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool)
    (bits : Fin (repetitionCount delta*wordWidth (context A C K j epsilon z v)) → Bool) : ℚ :=
  TreeFraction.val (output ((context A C K j epsilon z v,repetitionCount delta),
    ((degree,depth),List.ofFn bits)))

/-- Exact observable transport, including the outputs on inaccurate
sample histories, lets the original median analysis apply unchanged. -/
theorem sameLaw (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (epsilon delta : ℚ) (he : 0 < epsilon)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree
      (roundingTolerance (innerTolerance (epsilon/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth
      (roundingTolerance (innerTolerance (epsilon/2) j))) :
    SameLaw (value A C K j epsilon delta z v degree depth)
      (RootedOracleDensity.medianEstimate A (RootedCompletion.rowColumn A.T) C z K hK hW j
        epsilon delta (RootedCatalogGrid.gridEquiv A K v)) := by
  have heh : 0 < epsilon/2 := by positivity
  have hs := RootedEstimatorWordProgram.sameLaw_word A C K j hC hj hK hW hB
    (epsilon/2) 1 heh (by norm_num) z hz v degree depth hdegree hdepth
  have hp := (hs.independent (repetitionCount delta)).map
    (fun qs : Fin (repetitionCount delta) → ℚ => rationalMedian (List.ofFn qs))
  have hw := RootedEstimatorWordProgram.scheduledWidth_positive A C K j hC hK
    (innerTolerance (epsilon/2) j) 1 (innerTolerance_pos (epsilon/2) j heh)
      (by norm_num) z v
  intro phi
  have hleft := uniformAverage_equiv
    (gridWordEquiv (repetitionCount delta) (wordWidth (context A C K j epsilon z v)))
    (fun xs => phi (rationalMedian (List.ofFn (fun i => TreeFraction.val
      (RootedEstimatorWordProgram.output (RootedEstimatorWordProgram.input
        (context A C K j epsilon z v) (degree,depth) (xs i)))))))
  have hright := uniformAverage_equiv
    (oracleWalkWordEquiv (repetitionCount delta)
      (estimatorWordBits A C K j (innerTolerance (epsilon/2) j) 1))
    (fun xs => phi (rationalMedian (List.ofFn (fun i => RootedOracleDensity.wordEstimate A
      (RootedCompletion.rowColumn A.T) C z K hK hW j (epsilon/2) 1
        (RootedCatalogGrid.gridEquiv A K v) (xs i)))))
  have hout : uniformAverage (fun bits => phi (value A C K j epsilon delta z v degree depth bits))=
      uniformAverage (fun bits => phi (rationalMedian (List.ofFn (fun i : Fin (repetitionCount delta) =>
        TreeFraction.val (RootedEstimatorWordProgram.output (RootedEstimatorWordProgram.input
          (context A C K j epsilon z v) (degree,depth)
            (gridWordEquiv (repetitionCount delta) (wordWidth (context A C K j epsilon z v)) bits i))))))) := by
    apply congrArg uniformAverage
    funext bits
    exact congrArg phi (output_ofFn (context A C K j epsilon z v) (repetitionCount delta)
      hw (degree,depth) bits)
  exact hout.trans (hleft.trans ((hp phi).trans hright.symm))

theorem success (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (epsilon delta : ℚ) (he0 : 0 < epsilon) (he1 : epsilon < 1) (hd : 0 < delta)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree
      (roundingTolerance (innerTolerance (epsilon/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth
      (roundingTolerance (innerTolerance (epsilon/2) j)))
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K)) :
    1-(delta:ℝ) ≤ uniformAverage
      (fun bits : Fin (repetitionCount delta*wordWidth (context A C K j epsilon z v)) → Bool =>
        if (1-(epsilon:ℝ))*RootedCountIdentification.h A (RootedCompletion.rowColumn A.T)
            ((j:ℝ)*C/height A C) z ≤ (value A C K j epsilon delta z v degree depth bits:ℝ) ∧
          (value A C K j epsilon delta z v degree depth bits:ℝ) ≤
            (1+(epsilon:ℝ))*RootedCountIdentification.h A (RootedCompletion.rowColumn A.T)
              ((j:ℝ)*C/height A C) z then (1:ℝ) else 0) := by
  let event := fun q : ℚ => if
    (1-(epsilon:ℝ))*RootedCountIdentification.h A (RootedCompletion.rowColumn A.T)
        ((j:ℝ)*C/height A C) z ≤ (q:ℝ) ∧
    (q:ℝ) ≤ (1+(epsilon:ℝ))*RootedCountIdentification.h A (RootedCompletion.rowColumn A.T)
      ((j:ℝ)*C/height A C) z then (1:ℝ) else 0
  have heq := sameLaw A C K j hC hj hK hW hB epsilon delta he0 z hz v degree depth hdegree hdepth event
  exact (RootedOracleDensity.medianEstimate_success A (RootedCompletion.rowColumn A.T) C hC z hz
    K hK hW hB j hj epsilon delta he0 he1 hd hPL hCheeger
      (RootedCatalogGrid.gridEquiv A K v)).trans_eq heq.symm

end
end ContingencyTables.RootedEstimatorMedianProgram

end OAI
