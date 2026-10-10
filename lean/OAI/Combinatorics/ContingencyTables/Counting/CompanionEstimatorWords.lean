import OAI.Combinatorics.ContingencyTables.Counting.CompanionEstimatorConfidence
import OAI.Combinatorics.ContingencyTables.Counting.CompanionEstimatorRange

namespace OAI

/-! # A single Boolean word for the literal companion weight estimator -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteIndependentAverages FairBits
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The complete input length, with one independent walk for each ratio
sample and one walk plus integer-bin draw for each correction sample. -/
def estimatorWordBits (A : Instance I J) (C K j : ℕ) (delta failure : ℚ) : ℕ :=
  j*(sampleCount j delta failure *
    (oracleTime A C K 1 delta * oracleStepBits A C)) +
  sampleCount j delta failure *
    oracleIntegerBits A C (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta)

lemma estimatorWordBits_eq (A : Instance I J) (C K j : ℕ) (delta failure : ℚ) :
    estimatorWordBits A C K j delta failure = sampleCount j delta failure *
      (j*oracleTime A C K 1 delta*oracleStepBits A C +
        oracleTime A C K 1 (correctionTheta delta)*oracleStepBits A C +
        binWordBits A (offsetAccuracy A delta)) := by
  unfold estimatorWordBits oracleIntegerBits
  ring

def ratioBlockWordEquiv (A : Instance I J) (C K j : ℕ) (delta failure : ℚ) :
    (Fin (sampleCount j delta failure *
      (oracleTime A C K 1 delta * oracleStepBits A C)) → Bool) ≃
    RatioBlock A C K j delta failure :=
  (oracleWalkWordEquiv (sampleCount j delta failure)
      (oracleTime A C K 1 delta * oracleStepBits A C)).trans
    (Equiv.piCongrRight (fun _ =>
      oracleWalkWordEquiv (oracleTime A C K 1 delta) (oracleStepBits A C)))

/-- This equivalence partitions, rather than reuses, the random bits of
all the individual experiments in the estimator. -/
def estimatorWordEquiv (A : Instance I J) (C K j : ℕ) (delta failure : ℚ) :
    (Fin (estimatorWordBits A C K j delta failure) → Bool) ≃
      EstimatorInput A C K j delta failure :=
  (splitWordEquiv _ _).trans (Equiv.prodCongr
    ((oracleWalkWordEquiv j (sampleCount j delta failure *
      (oracleTime A C K 1 delta * oracleStepBits A C))).trans
        (Equiv.piCongrRight (fun _ => ratioBlockWordEquiv A C K j delta failure)))
    (oracleWalkWordEquiv (sampleCount j delta failure)
      (oracleIntegerBits A C (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta))))

def wordEstimate (A : Instance I J) (C : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (j : ℕ) (epsilon failure : ℚ)
    (v : Grid (I := Fin (dimension A)) K)
    (bits : Fin (estimatorWordBits A C K j (innerTolerance epsilon j) failure) → Bool) : ℚ :=
  estimateValue A C z K hK hW j (innerTolerance epsilon j) failure v
    (estimatorWordEquiv A C K j (innerTolerance epsilon j) failure bits)

/-- The single fixed-length word has exactly the independent-product law. -/
theorem wordEstimate_failure (A : Instance I J) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C)
    (epsilon failure : ℚ) (he0 : 0 < epsilon) (he1 : epsilon < 1) (hf : 0 < failure)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    uniformAverage (fun bits : Fin (estimatorWordBits A C K j (innerTolerance epsilon j) failure) → Bool =>
      if (wordEstimate A C z K hK hW j epsilon failure v bits:ℝ) <
          (1-(epsilon:ℝ))*h A ((j:ℝ)*C/height A C) z ∨
        (1+(epsilon:ℝ))*h A ((j:ℝ)*C/height A C) z <
          (wordEstimate A C z K hK hW j epsilon failure v bits:ℝ)
      then (1:ℝ) else 0) ≤ (failure:ℝ)/4 := by
  let test := fun draws : EstimatorInput A C K j (innerTolerance epsilon j) failure =>
      if (estimateValue A C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ) <
          (1-(epsilon:ℝ))*h A ((j:ℝ)*C/height A C) z ∨
        (1+(epsilon:ℝ))*h A ((j:ℝ)*C/height A C) z <
          (estimateValue A C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ)
      then (1:ℝ) else 0
  have he := uniformAverage_equiv
    (estimatorWordEquiv A C K j (innerTolerance epsilon j) failure) test
  change uniformAverage (fun bits => test
    (estimatorWordEquiv A C K j (innerTolerance epsilon j) failure bits)) ≤ _
  exact he.trans_le
    (estimateValue_failure A C hC z hz K hK hW hB j hj epsilon failure he0 he1 hf hPL hCheeger v)

theorem wordEstimate_range (A : Instance I J) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C)
    (epsilon failure : ℚ) (he0 : 0 < epsilon) (he1 : epsilon < 1) (hf : 0 < failure)
    (v : Grid (I := Fin (dimension A)) K)
    (bits : Fin (estimatorWordBits A C K j (innerTolerance epsilon j) failure) → Bool) :
    (assignmentCount A:ℝ)*(1/2:ℝ)^j/16 ≤
      (wordEstimate A C z K hK hW j epsilon failure v bits:ℝ) ∧
    (wordEstimate A C z K hK hW j epsilon failure v bits:ℝ) ≤ 8*assignmentCount A :=
  estimateValue_range A C hC z hz K hK hW hB j hj (innerTolerance epsilon j) failure
    (innerTolerance_pos epsilon j he0) (innerTolerance_lt_one epsilon j he1) hf v _

end

end ContingencyTables.CompanionOracleDensity

end OAI
