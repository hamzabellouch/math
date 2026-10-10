import OAI.Combinatorics.ContingencyTables.Counting.CompanionOracleEstimator

namespace OAI

/-! # Confidence of the complete bounded-word weight estimator -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteIndependentAverages
open scoped BigOperators Classical

noncomputable section

lemma average_fintype_irrel {X : Type*} (s t : Fintype X) (f : X → ℝ) :
    @uniformAverage X s f=@uniformAverage X t f := by
  cases Subsingleton.elim s t
  rfl

variable {I J : Type*} [Fintype I] [Fintype J]

def badFactor (A : Instance I J) (C : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (j : ℕ) (delta failure : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (i : Option (Fin j))
    (draws : EstimatorInput A C K j delta failure) : Prop :=
  (delta:ℝ)*targetFactor A C z K hK hW j i <
    |(observedFactor A C z K hK hW j delta failure v draws i:ℝ)-targetFactor A C z K hK hW j i|

lemma factor_failure (A : Instance I J) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C)
    (delta failure : ℚ) (hd0 : 0 < delta) (hd1 : delta < 1) (hf : 0 < failure)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (i : Option (Fin j)) :
    uniformAverage (fun draws : EstimatorInput A C K j delta failure =>
      if badFactor A C z K hK hW j delta failure v i draws then (1:ℝ) else 0) ≤
        (failure:ℝ)/(4*((j:ℝ)+1)) := by
  let : Nonempty (Fin j → RatioBlock A C K j delta failure) := ⟨fun _ _ _ _ => false⟩
  let : Nonempty (CorrectionBlock A C K j delta failure) := ⟨fun _ _ => false⟩
  cases i with
  | none =>
    simp only [badFactor,observedFactor,targetFactor,rationalAverage_cast]
    convert scheduled_correction_failure A C j j hC hj delta failure hd0 hd1 hf z hz K hK hW hB hPL hCheeger v using 1
    rw [uniformAverage_prod]
    dsimp only
    convert uniformAverage_const (X := Fin j → RatioBlock A C K j delta failure)
      (uniformAverage (fun draws : CorrectionBlock A C K j delta failure =>
        if (delta:ℝ)*correctionMean A C j z K hK hW <
          |sampleAverage (fun bits => (correctionSample A C j z K hK hW (roundingTolerance delta) v
            (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta) bits:ℝ))
            (sampleCount j delta failure) draws-correctionMean A C j z K hK hW| then 1 else 0)) using 1
  | some a =>
    simp only [badFactor,observedFactor,targetFactor,rationalAverage_cast]
    convert scheduled_ratio_failure A C a.val j hC (by omega) delta failure hd0 hf z hz K hK hB hPL hCheeger v using 1
    rw [uniformAverage_prod]
    dsimp only
    have hc (x : Fin j → RatioBlock A C K j delta failure) :=
      uniformAverage_const (X := CorrectionBlock A C K j delta failure)
        (if (delta:ℝ)*ratioMean A C a.val z K <
          |sampleAverage (fun bits => (ratioSample A C a.val z v (oracleTime A C K 1 delta) bits:ℝ))
            (sampleCount j delta failure) (x a)-ratioMean A C a.val z K| then 1 else 0)
    simp_rw [hc]
    convert uniformAverage_coordinate (X := fun _ : Fin j => RatioBlock A C K j delta failure) a (fun draws : RatioBlock A C K j delta failure =>
      if (delta:ℝ)*ratioMean A C a.val z K <
          |sampleAverage (fun bits => (ratioSample A C a.val z v (oracleTime A C K 1 delta) bits:ℝ))
            (sampleCount j delta failure) draws-ratioMean A C a.val z K| then 1 else 0) using 1
    exact average_fintype_irrel _ _ _

/-- All ratio and correction block failures share one explicit budget.
The statement concerns the actual bounded Boolean experiment. -/
theorem goodEstimate_failure (A : Instance I J) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C)
    (delta failure : ℚ) (hd0 : 0 < delta) (hd1 : delta < 1) (hf : 0 < failure)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    uniformAverage (fun draws : EstimatorInput A C K j delta failure =>
      if ¬GoodEstimate A C z K hK hW j delta failure v draws then (1:ℝ) else 0) ≤ (failure:ℝ)/4 := by
  have he (draws : EstimatorInput A C K j delta failure) :
      (¬GoodEstimate A C z K hK hW j delta failure v draws) ↔
        ∃ i,badFactor A C z K hK hW j delta failure v i draws := by
    simp only [GoodEstimate,badFactor,not_forall,not_le]
  simp_rw [he]
  calc
    _ ≤ ∑ i : Option (Fin j),uniformAverage (fun draws : EstimatorInput A C K j delta failure =>
        if badFactor A C z K hK hW j delta failure v i draws then (1:ℝ) else 0) :=
      uniform_union_bound _
    _ ≤ ∑ _i : Option (Fin j),(failure:ℝ)/(4*((j:ℝ)+1)) :=
      Finset.sum_le_sum (fun i _ => factor_failure A C hC z hz K hK hW hB j hj delta failure
        hd0 hd1 hf hPL hCheeger v i)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_option,Fintype.card_fin,nsmul_eq_mul,
        Nat.cast_add,Nat.cast_one]
      field_simp

lemma innerTolerance_pos (epsilon : ℚ) (j : ℕ) (he : 0 < epsilon) :
    0 < innerTolerance epsilon j := by unfold innerTolerance; positivity

lemma innerTolerance_lt_one (epsilon : ℚ) (j : ℕ) (he : epsilon < 1) :
    innerTolerance epsilon j < 1 := by
  unfold innerTolerance
  rw [div_lt_iff₀ (by positivity : (0:ℚ)<200*(j+1))]
  have hj : (0:ℚ) ≤ j := Nat.cast_nonneg _
  nlinarith

/-- A concrete rational estimator with bounded independent Boolean input
has the required relative-error guarantee for the original h-value. -/
theorem estimateValue_failure (A : Instance I J) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C)
    (epsilon failure : ℚ) (he0 : 0 < epsilon) (he1 : epsilon < 1) (hf : 0 < failure)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    uniformAverage (fun draws : EstimatorInput A C K j (innerTolerance epsilon j) failure =>
      if (estimateValue A C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ) <
          (1-(epsilon:ℝ))*h A ((j:ℝ)*C/height A C) z ∨
        (1+(epsilon:ℝ))*h A ((j:ℝ)*C/height A C) z <
          (estimateValue A C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ)
      then (1:ℝ) else 0) ≤ (failure:ℝ)/4 := by
  have ht : 0 ≤ h A ((j:ℝ)*C/height A C) z := (h_positive A _ _).le
  have heR : (0:ℝ) < epsilon := by exact_mod_cast he0
  have hp (draws : EstimatorInput A C K j (innerTolerance epsilon j) failure) :
      (if (estimateValue A C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ) <
          (1-(epsilon:ℝ))*h A ((j:ℝ)*C/height A C) z ∨
        (1+(epsilon:ℝ))*h A ((j:ℝ)*C/height A C) z <
          (estimateValue A C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ)
      then (1:ℝ) else 0) ≤
        if ¬GoodEstimate A C z K hK hW j (innerTolerance epsilon j) failure v draws then 1 else 0 := by
    by_cases hg : GoodEstimate A C z K hK hW j (innerTolerance epsilon j) failure v draws
    · have ha := goodEstimate_accuracy A C hC z hz K hK hW hB j hj epsilon failure he0 he1 v draws hg
      have hn : ¬((estimateValue A C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ) <
          (1-(epsilon:ℝ))*h A ((j:ℝ)*C/height A C) z ∨
        (1+(epsilon:ℝ))*h A ((j:ℝ)*C/height A C) z <
          (estimateValue A C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ)) := by
        rintro (hb|hb) <;> nlinarith
      simp only [hn,hg,not_true_eq_false,ite_false,le_refl]
    · simp only [hg,not_false_eq_true,ite_true]
      split_ifs <;> norm_num
  exact (uniformAverage_mono _ _ hp).trans
    (goodEstimate_failure A C hC z hz K hK hW hB j hj (innerTolerance epsilon j) failure
      (innerTolerance_pos epsilon j he0) (innerTolerance_lt_one epsilon j he1) hf hPL hCheeger v)

end

end ContingencyTables.CompanionOracleDensity

end OAI
