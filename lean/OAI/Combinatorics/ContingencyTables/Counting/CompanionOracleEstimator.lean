import OAI.Combinatorics.ContingencyTables.Counting.CompanionOracleSchedule
import OAI.Combinatorics.ContingencyTables.Transport.FiniteIndependentFailures
import OAI.Combinatorics.ContingencyTables.Transport.FiniteProductAccuracy

namespace OAI

/-! # The literal rational product estimator for a companion h-value -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteLawMoments FiniteIndependentAverages
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def rationalAverage {X : Type*} (g : X → ℚ) (N : ℕ) (draws : Fin N → X) : ℚ :=
  (∑ i,g (draws i))/N

lemma rationalAverage_cast {X : Type*} (g : X → ℚ) (N : ℕ) (draws : Fin N → X) :
    (rationalAverage g N draws:ℝ)=sampleAverage (fun x => (g x:ℝ)) N draws := by
  simp only [rationalAverage,Rat.cast_div,Rat.cast_sum,Rat.cast_natCast,sampleAverage,sampleSum]

abbrev RatioBlock (A : Instance I J) (C K j : ℕ) (delta failure : ℚ) :=
  Fin (sampleCount j delta failure) → RatioWords A C (oracleTime A C K 1 delta)

abbrev CorrectionBlock (A : Instance I J) (C K j : ℕ) (delta failure : ℚ) :=
  Fin (sampleCount j delta failure) →
    (Fin (oracleIntegerBits A C (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta)) → Bool)

abbrev EstimatorInput (A : Instance I J) (C K j : ℕ) (delta failure : ℚ) :=
  (Fin j → RatioBlock A C K j delta failure) × CorrectionBlock A C K j delta failure

def observedFactor (A : Instance I J) (C : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (j : ℕ) (delta failure : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (draws : EstimatorInput A C K j delta failure) :
    Option (Fin j) → ℚ
  | none => rationalAverage
      (correctionSample A C j z K hK hW (roundingTolerance delta) v
        (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta))
      (sampleCount j delta failure) draws.2
  | some a => rationalAverage
      (ratioSample A C a.val z v (oracleTime A C K 1 delta))
      (sampleCount j delta failure) (draws.1 a)

def targetFactor (A : Instance I J) (C : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (j : ℕ) : Option (Fin j) → ℝ
  | none => correctionMean A C j z K hK hW
  | some a => ratioMean A C a.val z K

def estimateValue (A : Instance I J) (C : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (j : ℕ) (delta failure : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (draws : EstimatorInput A C K j delta failure) : ℚ :=
  (assignmentCount A:ℚ)*∏ i,observedFactor A C z K hK hW j delta failure v draws i

/-- The exact means appearing in the implemented product telescope to
h, including the integer-population correction and the free-assignment count. -/
theorem targetFactor_product (A : Instance I J) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (j : ℕ) :
    (assignmentCount A:ℝ)*(∏ i,targetFactor A C z K hK hW j i)=
      h A ((j:ℝ)*C/height A C) z := by
  have hp : (∏ a : Fin j,ratioMean A C a.val z K)=
      ∏ a∈Finset.range j,ratioMean A C a z K :=
    Fin.prod_univ_eq_prod_range (fun a : ℕ => ratioMean A (C:ℝ) a z K) j
  rw [Fintype.prod_option]
  simp only [targetFactor]
  rw [hp,correctionMean_eq]
  have ht := oracle_telescope A C (by exact_mod_cast hC) z K (by omega) j
  convert ht using 1; ring

lemma targetFactor_positive (A : Instance I J) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C) (i : Option (Fin j)) :
    0 < targetFactor A C z K hK hW j i := by
  cases i with
  | none =>
    have hh := (correctionMean_bounds A C j hC hj z K hK hW hB).1
    change 0 < correctionMean A C j z K hK hW
    linarith
  | some a =>
    have hh := (ratioMean_bounds A C a.val hC z hz hK hB.le).1
    change 0 < ratioMean A C a.val z K
    linarith

def GoodEstimate (A : Instance I J) (C : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (j : ℕ) (delta failure : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (draws : EstimatorInput A C K j delta failure) : Prop :=
  ∀ i,|(observedFactor A C z K hK hW j delta failure v draws i:ℝ)-targetFactor A C z K hK hW j i| ≤
    (delta:ℝ)*targetFactor A C z K hK hW j i

def innerTolerance (epsilon : ℚ) (j : ℕ) : ℚ := epsilon/(200*(j+1))

/-- On the event certified by the actual independent block experiments,
the returned rational product estimates the literal original h-value. -/
theorem goodEstimate_accuracy (A : Instance I J) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C)
    (epsilon failure : ℚ) (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (v : Grid (I := Fin (dimension A)) K)
    (draws : EstimatorInput A C K j (innerTolerance epsilon j) failure)
    (hgood : GoodEstimate A C z K hK hW j (innerTolerance epsilon j) failure v draws) :
    (1-(epsilon:ℝ)/4)*h A ((j:ℝ)*C/height A C) z ≤
        (estimateValue A C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ) ∧
      (estimateValue A C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ) ≤
        (1+(epsilon:ℝ)/4)*h A ((j:ℝ)*C/height A C) z := by
  have htol : (innerTolerance epsilon j:ℝ)=
      (epsilon:ℝ)/(200*(Fintype.card (Option (Fin j)):ℝ)) := by
    simp only [innerTolerance,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_add,
      Rat.cast_natCast,Rat.cast_one,Fintype.card_option,Fintype.card_fin,Nat.cast_add,Nat.cast_one]
  have hprod := FiniteProductAccuracy.product_relative
    (fun i => (observedFactor A C z K hK hW j (innerTolerance epsilon j) failure v draws i:ℝ))
    (targetFactor A C z K hK hW j) (targetFactor_positive A C hC z hz K hK hW hB j hj)
    epsilon (by exact_mod_cast he0) (by exact_mod_cast he1)
    (by intro i; rw [←htol]; exact hgood i) (by simp)
  have hcount : (0:ℝ) ≤ assignmentCount A := Nat.cast_nonneg _
  have hlow := mul_le_mul_of_nonneg_left hprod.1 hcount
  have hupp := mul_le_mul_of_nonneg_left hprod.2 hcount
  have htarget := targetFactor_product A C hC z K hK hW j
  have hvalue : (estimateValue A C z K hK hW j (innerTolerance epsilon j) failure v draws:ℝ)=
      (assignmentCount A:ℝ)*∏ i,
        (observedFactor A C z K hK hW j (innerTolerance epsilon j) failure v draws i:ℝ) := by
    simp only [estimateValue,Rat.cast_mul,Rat.cast_natCast,Rat.cast_prod]
  rw [hvalue]
  rw [←htarget]
  constructor
  · simpa only [mul_left_comm] using hlow
  · simpa only [mul_left_comm] using hupp

end

end ContingencyTables.CompanionOracleDensity

end OAI
