import OAI.Combinatorics.ContingencyTables.Counting.CompanionEstimatorWords
import OAI.Combinatorics.ContingencyTables.Transport.FiniteMedianConfidence

namespace OAI

/-! # Logarithmic confidence amplification of the actual weight estimator -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteMedianConfidence
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Each complete estimator uses constant confidence; the requested
failure probability changes only the number of independent medians. -/
def medianEstimatorBits (A : Instance I J) (C K j : ℕ) (epsilon delta : ℚ) : ℕ :=
  repetitionCount delta * estimatorWordBits A C K j (innerTolerance (epsilon/2) j) 1

def medianEstimate (A : Instance I J) (C : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (j : ℕ) (epsilon delta : ℚ)
    (v : Grid (I := Fin (dimension A)) K)
    (bits : Fin (medianEstimatorBits A C K j epsilon delta) → Bool) : ℚ :=
  rationalMedian (List.ofFn (fun i : Fin (repetitionCount delta) =>
    wordEstimate A C z K hK hW j (epsilon/2) 1 v
      (oracleWalkWordEquiv (repetitionCount delta)
        (estimatorWordBits A C K j (innerTolerance (epsilon/2) j) 1) bits i)))

theorem medianEstimate_success (A : Instance I J) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C)
    (epsilon delta : ℚ) (he0 : 0 < epsilon) (he1 : epsilon < 1) (hd : 0 < delta)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    1-(delta:ℝ) ≤ uniformAverage (fun bits : Fin (medianEstimatorBits A C K j epsilon delta) → Bool =>
      if (1-(epsilon:ℝ))*h A ((j:ℝ)*C/height A C) z ≤
          (medianEstimate A C z K hK hW j epsilon delta v bits:ℝ) ∧
        (medianEstimate A C z K hK hW j epsilon delta v bits:ℝ) ≤
          (1+(epsilon:ℝ))*h A ((j:ℝ)*C/height A C) z
      then (1:ℝ) else 0) := by
  have heh0 : 0 < epsilon/2 := by positivity
  have heh1 : epsilon/2 < 1 := by linarith
  have ht : 0 < h A ((j:ℝ)*C/height A C) z := h_positive A _ _
  have heR : (0:ℝ) < epsilon := by exact_mod_cast he0
  have hbase := wordEstimate_failure A C hC z hz K hK hW hB j hj (epsilon/2) 1 heh0 heh1
    (by norm_num) hPL hCheeger v
  have hbad : uniformAverage (fun bits : Fin (estimatorWordBits A C K j (innerTolerance (epsilon/2) j) 1) → Bool =>
      if (wordEstimate A C z K hK hW j (epsilon/2) 1 v bits:ℝ) <
          (1-(epsilon:ℝ)/2)*h A ((j:ℝ)*C/height A C) z ∨
        (1+(epsilon:ℝ)/2)*h A ((j:ℝ)*C/height A C) z <
          (wordEstimate A C z K hK hW j (epsilon/2) 1 v bits:ℝ)
      then (1:ℝ) else 0) ≤ 5/16 := by
    have hh : (1:ℝ)/4 ≤ 5/16 := by norm_num
    apply le_trans ?_ hh
    simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using hbase
  have hm := median_confidence_real
    (wordEstimate A C z K hK hW j (epsilon/2) 1 v)
    ((1-(epsilon:ℝ))*h A ((j:ℝ)*C/height A C) z)
    ((1-(epsilon:ℝ)/2)*h A ((j:ℝ)*C/height A C) z)
    ((1+(epsilon:ℝ)/2)*h A ((j:ℝ)*C/height A C) z)
    ((1+(epsilon:ℝ))*h A ((j:ℝ)*C/height A C) z)
    (by nlinarith) (by nlinarith) delta hd hbad
  let test := fun xs : Fin (repetitionCount delta) →
      (Fin (estimatorWordBits A C K j (innerTolerance (epsilon/2) j) 1) → Bool) =>
      if (1-(epsilon:ℝ))*h A ((j:ℝ)*C/height A C) z ≤
          (rationalMedian (List.ofFn (fun i => wordEstimate A C z K hK hW j (epsilon/2) 1 v (xs i))):ℝ) ∧
        (rationalMedian (List.ofFn (fun i => wordEstimate A C z K hK hW j (epsilon/2) 1 v (xs i))):ℝ) ≤
          (1+(epsilon:ℝ))*h A ((j:ℝ)*C/height A C) z
      then (1:ℝ) else 0
  have he := uniformAverage_equiv
    (oracleWalkWordEquiv (repetitionCount delta)
      (estimatorWordBits A C K j (innerTolerance (epsilon/2) j) 1)) test
  change 1-(delta:ℝ) ≤ uniformAverage (fun bits => test
      (oracleWalkWordEquiv (repetitionCount delta)
        (estimatorWordBits A C K j (innerTolerance (epsilon/2) j) 1) bits))
  exact hm.trans_eq he.symm

/-- Amplification also preserves the proved range on every word,
including statistically unsuccessful words. -/
theorem medianEstimate_range (A : Instance I J) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C)
    (epsilon delta : ℚ) (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (v : Grid (I := Fin (dimension A)) K)
    (bits : Fin (medianEstimatorBits A C K j epsilon delta) → Bool) :
    (assignmentCount A:ℝ)*(1/2:ℝ)^j/16 ≤
      (medianEstimate A C z K hK hW j epsilon delta v bits:ℝ) ∧
    (medianEstimate A C z K hK hW j epsilon delta v bits:ℝ) ≤ 8*assignmentCount A := by
  let samples := List.ofFn (fun i : Fin (repetitionCount delta) =>
    wordEstimate A C z K hK hW j (epsilon/2) 1 v
      (oracleWalkWordEquiv (repetitionCount delta)
        (estimatorWordBits A C K j (innerTolerance (epsilon/2) j) 1) bits i))
  have hmem := rationalMedian_mem samples (by
    dsimp only [samples]
    rw [List.length_ofFn]
    exact repetitionCount_pos delta)
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hmem
  have hr := wordEstimate_range A C hC z hz K hK hW hB j hj (epsilon/2) 1
    (by positivity) (by linarith) (by norm_num) v
    (oracleWalkWordEquiv (repetitionCount delta)
      (estimatorWordBits A C K j (innerTolerance (epsilon/2) j) 1) bits i)
  change _ ≤ (rationalMedian samples:ℝ) ∧ (rationalMedian samples:ℝ) ≤ _
  rw [←hi]
  exact hr

/-- The exact bit budget grows linearly with the binary confidence
parameter, rather than with its reciprocal. -/
lemma medianEstimatorBits_eq (A : Instance I J) (C K j : ℕ) (epsilon delta : ℚ) :
    medianEstimatorBits A C K j epsilon delta =
      64*(delta.den.bits.length+1) *
        estimatorWordBits A C K j (innerTolerance (epsilon/2) j) 1 := rfl

end

end ContingencyTables.CompanionOracleDensity

end OAI
