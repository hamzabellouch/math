import OAI.Combinatorics.ContingencyTables.Rooted.RootedEstimatorBlockProgram
import OAI.Combinatorics.ContingencyTables.Rooted.RootedCorrectionSampleLaw
import OAI.Combinatorics.ContingencyTables.Rooted.RootedRatioSampleLaw
import OAI.Combinatorics.ContingencyTables.Rooted.RootedEstimatorConfidence

namespace OAI

/-! # The executed blocks have the complete estimator law

Only the physical sample programs differ from the original enumeration.
Exact independent-observable transport identifies their whole product
estimator, including every event used by the confidence proof.
-/

namespace ContingencyTables.RootedComputedEstimator

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity FirstSuccess ResidualMixture FiniteObservableTransport
open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

abbrev RatioWords (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (delta failure : ℚ) :=
  Fin (sampleCount j delta failure) →
    (Fin (oracleTime A C K 1 delta*oracleStepBits A C) → Bool)

abbrev CorrectionWords (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (delta failure : ℚ) :=
  Fin (sampleCount j delta failure) → RootedCorrectionSampleLaw.Words A C
    (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta)

abbrev Inputs (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (delta failure : ℚ) :=
  (Fin j → RatioWords A C K j delta failure) × CorrectionWords A C K j delta failure

def ratioAverage (A : Instance (Fin m) (Fin n)) (C K j a : ℕ)
    (delta failure : ℚ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (draws : RatioWords A C K j delta failure) : ℚ :=
  (∑ i,RootedRatioSampleLaw.sample A C a z v (oracleTime A C K 1 delta) (draws i))/
    sampleCount j delta failure

def correctionAverage (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (delta failure : ℚ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (draws : CorrectionWords A C K j delta failure) : ℚ :=
  (∑ i,RootedCorrectionSampleLaw.sample A C j K hK hW z (roundingTolerance delta) v
    (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta) (draws i))/
      sampleCount j delta failure

def estimate (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (delta failure : ℚ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (draws : Inputs A C K j delta failure) : ℚ :=
  (assignmentCount A:ℚ)*(∏ a : Fin j,ratioAverage A C K j a.val delta failure z v (draws.1 a))*
    correctionAverage A C K j hK hW delta failure z v draws.2

private lemma ratioAverage_law (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hB : (K:ℝ)=binWidth A C) (delta failure : ℚ) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (a : Fin j) :
    SameLaw (ratioAverage A C K j a.val delta failure z v)
      (fun draws : CompanionOracleDensity.RatioBlock A C K j delta failure =>
        rationalAverage (RootedOracleDensity.ratioSample A (RootedCompletion.rowColumn A.T)
          C a.val z (RootedCatalogGrid.gridEquiv A K v) (oracleTime A C K 1 delta))
            (sampleCount j delta failure) draws) := by
  have hsample := RootedRatioSampleLaw.sameLaw A C a.val K hC
    (show a.val ≤ rationalHeight A C from Nat.le_trans (Nat.le_of_lt a.isLt) hj)
    hK hB.le z hz v (oracleTime A C K 1 delta)
  exact (hsample.independent (sampleCount j delta failure)).map
    (fun qs : Fin (sampleCount j delta failure) → ℚ => (∑ i,qs i)/sampleCount j delta failure)

private lemma correctionAverage_law (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C) (delta failure : ℚ)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    SameLaw (correctionAverage A C K j hK hW delta failure z v)
      (fun draws : CompanionOracleDensity.CorrectionBlock A C K j delta failure =>
        rationalAverage (RootedOracleDensity.correctionSample A (RootedCompletion.rowColumn A.T)
          C j z K hK hW (roundingTolerance delta) (RootedCatalogGrid.gridEquiv A K v)
          (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta))
            (sampleCount j delta failure) draws) := by
  have hsample : SameLaw
      (RootedCorrectionSampleLaw.sample A C j K hK hW z (roundingTolerance delta) v
        (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta))
      (RootedOracleDensity.correctionSample A (RootedCompletion.rowColumn A.T) C j z K hK hW
        (roundingTolerance delta) (RootedCatalogGrid.gridEquiv A K v)
        (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta)) :=
    RootedCorrectionSampleLaw.sample_average A C j K hC hj hK hW hB.le z hz
      (roundingTolerance delta) v _ _
  exact (hsample.independent (sampleCount j delta failure)).map
    (fun qs : Fin (sampleCount j delta failure) → ℚ => (∑ i,qs i)/sampleCount j delta failure)

/-- Exact equality of the whole rational estimator law; no extra oracle
or confidence hypothesis is introduced at the implementation boundary. -/
theorem sameLaw (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C) (delta failure : ℚ)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    SameLaw (estimate A C K j hK hW delta failure z v)
      (RootedOracleDensity.estimateValue A (RootedCompletion.rowColumn A.T) C z K hK hW j
        delta failure (RootedCatalogGrid.gridEquiv A K v)) := by
  let originalRatio := fun (a : Fin j) (draws : CompanionOracleDensity.RatioBlock A C K j delta failure) =>
    rationalAverage (RootedOracleDensity.ratioSample A (RootedCompletion.rowColumn A.T) C a.val z
      (RootedCatalogGrid.gridEquiv A K v) (oracleTime A C K 1 delta))
      (sampleCount j delta failure) draws
  let originalCorrection := fun draws : CompanionOracleDensity.CorrectionBlock A C K j delta failure =>
    rationalAverage (RootedOracleDensity.correctionSample A (RootedCompletion.rowColumn A.T)
      C j z K hK hW (roundingTolerance delta) (RootedCatalogGrid.gridEquiv A K v)
      (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta))
      (sampleCount j delta failure) draws
  have hr := FiniteObservableTransport.indexed j
    (fun a : Fin j => ratioAverage A C K j a.val delta failure z v) originalRatio
    (fun a => ratioAverage_law A C K j hC hj hK hB delta failure z hz v a)
  have hc := correctionAverage_law A C K j hC hj hK hW hB delta failure z hz v
  have ht := (hr.prod hc).map (fun p : (Fin j → ℚ)×ℚ => (assignmentCount A:ℚ)*(∏ a,p.1 a)*p.2)
  have ho (draws : EstimatorInput A C K j delta failure) :
      (assignmentCount A:ℚ)*(∏ a,originalRatio a (draws.1 a))*originalCorrection draws.2=
        RootedOracleDensity.estimateValue A (RootedCompletion.rowColumn A.T) C z K hK hW j
          delta failure (RootedCatalogGrid.gridEquiv A K v) draws := by
    rw [RootedOracleDensity.estimateValue,Fintype.prod_option]
    simp only [RootedOracleDensity.observedFactor,originalRatio,originalCorrection]
    ring
  intro phi
  have hh := ht phi
  change uniformAverage (fun draws : Inputs A C K j delta failure =>
      phi (estimate A C K j hK hW delta failure z v draws)) =
    uniformAverage (fun draws : EstimatorInput A C K j delta failure =>
      phi ((assignmentCount A:ℚ)*(∏ a,originalRatio a (draws.1 a))*
        originalCorrection draws.2)) at hh
  exact hh.trans (congrArg uniformAverage (funext (fun draws => congrArg phi (ho draws))))

end
end ContingencyTables.RootedComputedEstimator

end OAI
