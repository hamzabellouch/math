import OAI.Combinatorics.ContingencyTables.Rooted.RootedOracleEstimator
import OAI.Combinatorics.ContingencyTables.Counting.CompanionEstimatorConfidence

namespace OAI

/-! # Confidence of the complete bounded-word weight estimator -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteIndependentAverages
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def badFactor (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (j : ℕ) (delta failure : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (i : Option (Fin j))
    (draws : EstimatorInput A C K j delta failure) : Prop :=
  (delta:ℝ)*targetFactor A R C z K hK hW j i <
    |(observedFactor A R C z K hK hW j delta failure v draws i:ℝ)-targetFactor A R C z K hK hW j i|

lemma factor_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C)
    (delta failure : ℚ) (hd0 : 0 < delta) (hd1 : delta < 1) (hf : 0 < failure)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (i : Option (Fin j)) :
    uniformAverage (fun draws : EstimatorInput A C K j delta failure =>
      if badFactor A R C z K hK hW j delta failure v i draws then (1:ℝ) else 0) ≤
        (failure:ℝ)/(4*((j:ℝ)+1)) := by
  let : Nonempty (Fin j → RatioBlock A C K j delta failure) := ⟨fun _ _ _ _ => false⟩
  let : Nonempty (CorrectionBlock A C K j delta failure) := ⟨fun _ _ => false⟩
  cases i with
  | none =>
    simp only [badFactor,observedFactor,targetFactor,rationalAverage_cast]
    convert scheduled_correction_failure A R C j j hC hj delta failure hd0 hd1 hf z hz K hK hW hB hPL hCheeger v using 1
    rw [uniformAverage_prod]
    dsimp only
    convert uniformAverage_const (X := Fin j → RatioBlock A C K j delta failure)
      (uniformAverage (fun draws : CorrectionBlock A C K j delta failure =>
        if (delta:ℝ)*correctionMean A R C j z K hK hW <
          |sampleAverage (fun bits => (correctionSample A R C j z K hK hW (roundingTolerance delta) v
            (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta) bits:ℝ))
            (sampleCount j delta failure) draws-correctionMean A R C j z K hK hW| then 1 else 0)) using 1
  | some a =>
    simp only [badFactor,observedFactor,targetFactor,rationalAverage_cast]
    convert scheduled_ratio_failure A R C a.val j hC (by omega) delta failure hd0 hf z hz K hK hB hPL hCheeger v using 1
    rw [uniformAverage_prod]
    dsimp only
    have hc (x : Fin j → RatioBlock A C K j delta failure) :=
      uniformAverage_const (X := CorrectionBlock A C K j delta failure)
        (if (delta:ℝ)*ratioMean A R C a.val z K <
          |sampleAverage (fun bits => (ratioSample A R C a.val z v (oracleTime A C K 1 delta) bits:ℝ))
            (sampleCount j delta failure) (x a)-ratioMean A R C a.val z K| then 1 else 0)
    simp_rw [hc]
    convert uniformAverage_coordinate (X := fun _ : Fin j => RatioBlock A C K j delta failure) a (fun draws : RatioBlock A C K j delta failure =>
      if (delta:ℝ)*ratioMean A R C a.val z K <
          |sampleAverage (fun bits => (ratioSample A R C a.val z v (oracleTime A C K 1 delta) bits:ℝ))
            (sampleCount j delta failure) draws-ratioMean A R C a.val z K| then 1 else 0) using 1
    exact average_fintype_irrel _ _ _

/-- All ratio and correction block failures share one explicit budget.
The statement concerns the actual bounded Boolean experiment. -/
theorem goodEstimate_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C)
    (delta failure : ℚ) (hd0 : 0 < delta) (hd1 : delta < 1) (hf : 0 < failure)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    uniformAverage (fun draws : EstimatorInput A C K j delta failure =>
      if ¬GoodEstimate A R C z K hK hW j delta failure v draws then (1:ℝ) else 0) ≤ (failure:ℝ)/4 := by
  have he (draws : EstimatorInput A C K j delta failure) :
      (¬GoodEstimate A R C z K hK hW j delta failure v draws) ↔
        ∃ i,badFactor A R C z K hK hW j delta failure v i draws := by
    simp only [GoodEstimate,badFactor,not_forall,not_le]
  simp_rw [he]
  calc
    _ ≤ ∑ i : Option (Fin j),uniformAverage (fun draws : EstimatorInput A C K j delta failure =>
        if badFactor A R C z K hK hW j delta failure v i draws then (1:ℝ) else 0) :=
      uniform_union_bound _
    _ ≤ ∑ _i : Option (Fin j),(failure:ℝ)/(4*((j:ℝ)+1)) :=
      Finset.sum_le_sum (fun i _ => factor_failure A R C hC z hz K hK hW hB j hj delta failure
        hd0 hd1 hf hPL hCheeger v i)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_option,Fintype.card_fin,nsmul_eq_mul,
        Nat.cast_add,Nat.cast_one]
      field_simp

/-- A concrete rational estimator with bounded independent Boolean input
has the required relative-error guarantee for the original h-value. -/
theorem estimateValue_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C)
    (epsilon failure : ℚ) (he0 : 0 < epsilon) (he1 : epsilon < 1) (hf : 0 < failure)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    uniformAverage (fun draws : EstimatorInput A C K j (innerTolerance epsilon j) failure =>
      if (estimateValue A R C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ) <
          (1-(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z ∨
        (1+(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z <
          (estimateValue A R C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ)
      then (1:ℝ) else 0) ≤ (failure:ℝ)/4 := by
  have ht : 0 ≤ RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z := (RootedCountIdentification.h_positive A R _ _).le
  have heR : (0:ℝ) < epsilon := by exact_mod_cast he0
  have hp (draws : EstimatorInput A C K j (innerTolerance epsilon j) failure) :
      (if (estimateValue A R C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ) <
          (1-(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z ∨
        (1+(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z <
          (estimateValue A R C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ)
      then (1:ℝ) else 0) ≤
        if ¬GoodEstimate A R C z K hK hW j (innerTolerance epsilon j) failure v draws then 1 else 0 := by
    by_cases hg : GoodEstimate A R C z K hK hW j (innerTolerance epsilon j) failure v draws
    · have ha := goodEstimate_accuracy A R C hC z hz K hK hW hB j hj epsilon failure he0 he1 v draws hg
      have hn : ¬((estimateValue A R C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ) <
          (1-(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z ∨
        (1+(epsilon:ℝ))*RootedCountIdentification.h A R ((j:ℝ)*C/height A C) z <
          (estimateValue A R C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ)) := by
        rintro (hb|hb) <;> nlinarith
      simp only [hn,hg,not_true_eq_false,ite_false,le_refl]
    · simp only [hg,not_false_eq_true,ite_true]
      split_ifs <;> norm_num
  exact (uniformAverage_mono _ _ hp).trans
    (goodEstimate_failure A R C hC z hz K hK hW hB j hj (innerTolerance epsilon j) failure
      (innerTolerance_pos epsilon j he0) (innerTolerance_lt_one epsilon j he1) hf hPL hCheeger v)

end

end ContingencyTables.RootedOracleDensity

end OAI
