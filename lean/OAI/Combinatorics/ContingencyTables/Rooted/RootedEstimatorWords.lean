import OAI.Combinatorics.ContingencyTables.Rooted.RootedEstimatorConfidence
import OAI.Combinatorics.ContingencyTables.Rooted.RootedEstimatorRange
import OAI.Combinatorics.ContingencyTables.Counting.CompanionEstimatorWords

namespace OAI

/-! # A single Boolean word for the literal companion weight estimator -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteIndependentAverages FairBits
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def wordEstimate (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (j : ℕ) (epsilon failure : ℚ)
    (v : Grid (I := Fin (dimension A)) K)
    (bits : Fin (estimatorWordBits A C K j (innerTolerance epsilon j) failure) → Bool) : ℚ :=
  estimateValue A R C z K hK hW j (innerTolerance epsilon j) failure v
    (estimatorWordEquiv A C K j (innerTolerance epsilon j) failure bits)

/-- The single fixed-length word has exactly the previously analyzed
independent-product law. -/
theorem wordEstimate_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C)
    (epsilon failure : ℚ) (he0 : 0 < epsilon) (he1 : epsilon < 1) (hf : 0 < failure)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    uniformAverage (fun bits : Fin (estimatorWordBits A C K j (innerTolerance epsilon j) failure) → Bool =>
      if (wordEstimate A R C z K hK hW j epsilon failure v bits:ℝ) <
          (1-(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z ∨
        (1+(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z <
          (wordEstimate A R C z K hK hW j epsilon failure v bits:ℝ)
      then (1:ℝ) else 0) ≤ (failure:ℝ)/4 := by
  let test := fun draws : EstimatorInput A C K j (innerTolerance epsilon j) failure =>
      if (estimateValue A R C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ) <
          (1-(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z ∨
        (1+(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z <
          (estimateValue A R C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ)
      then (1:ℝ) else 0
  have he := uniformAverage_equiv
    (estimatorWordEquiv A C K j (innerTolerance epsilon j) failure) test
  change uniformAverage (fun bits => test
    (estimatorWordEquiv A C K j (innerTolerance epsilon j) failure bits)) ≤ _
  exact he.trans_le
    (estimateValue_failure A R C hC z hz K hK hW hB j hj epsilon failure he0 he1 hf hPL hCheeger v)

theorem wordEstimate_range (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C)
    (epsilon failure : ℚ) (he0 : 0 < epsilon) (he1 : epsilon < 1) (hf : 0 < failure)
    (v : Grid (I := Fin (dimension A)) K)
    (bits : Fin (estimatorWordBits A C K j (innerTolerance epsilon j) failure) → Bool) :
    (assignmentCount A:ℝ)*(1/2:ℝ)^j/16 ≤
      (wordEstimate A R C z K hK hW j epsilon failure v bits:ℝ) ∧
    (wordEstimate A R C z K hK hW j epsilon failure v bits:ℝ) ≤ 8*assignmentCount A :=
  estimateValue_range A R C hC z hz K hK hW hB j hj (innerTolerance epsilon j) failure
    (innerTolerance_pos epsilon j he0) (innerTolerance_lt_one epsilon j he1) hf v _

end

end ContingencyTables.RootedOracleDensity

end OAI
