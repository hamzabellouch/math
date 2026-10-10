import OAI.Combinatorics.ContingencyTables.Rooted.RootedOracleEstimator
import OAI.Combinatorics.ContingencyTables.Counting.CompanionEstimatorRange

namespace OAI

/-! # Output range on every execution of the finite-word estimator -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteIndependentAverages
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma observed_ratio_bounds (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (delta failure : ℚ) (hd : 0 < delta) (hf : 0 < failure)
    (v : Grid (I := Fin (dimension A)) K) (draws : EstimatorInput A C K j delta failure) (a : Fin j) :
    1/2 ≤ (observedFactor A R C z K hK hW j delta failure v draws (some a):ℝ) ∧
      (observedFactor A R C z K hK hW j delta failure v draws (some a):ℝ) ≤ 1 := by
  apply rationalAverage_bounds _ _ (sampleCount_positive j delta failure hd hf)
  intro bits
  rw [ratioSample_cast]
  exact ratioObservable_bounds A R C (by exact_mod_cast hC) a.val z hz hB.le _

lemma observed_correction_bounds (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (j : ℕ) (hj : j ≤ rationalHeight A C) (delta failure : ℚ) (hd : 0 < delta) (hd1 : delta < 1)
    (hf : 0 < failure) (v : Grid (I := Fin (dimension A)) K)
    (draws : EstimatorInput A C K j delta failure) :
    1/16 ≤ (observedFactor A R C z K hK hW j delta failure v draws none:ℝ) ∧
      (observedFactor A R C z K hK hW j delta failure v draws none:ℝ) ≤ 8 := by
  apply rationalAverage_bounds _ _ (sampleCount_positive j delta failure hd hf)
  intro bits
  apply computedCorrection_bounds A R C j hC hj z K (by omega) hW hB (roundingTolerance delta)
  · unfold roundingTolerance
    positivity
  · unfold roundingTolerance
    linarith

/-- These bounds hold for every Boolean input, including executions on
which the empirical averages are statistically inaccurate. -/
theorem estimateValue_range (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C)
    (delta failure : ℚ) (hd : 0 < delta) (hd1 : delta < 1) (hf : 0 < failure)
    (v : Grid (I := Fin (dimension A)) K) (draws : EstimatorInput A C K j delta failure) :
    (assignmentCount A:ℝ)*(1/2:ℝ)^j/16 ≤ (estimateValue A R C z K hK hW j delta failure v draws:ℝ) ∧
      (estimateValue A R C z K hK hW j delta failure v draws:ℝ) ≤ 8*assignmentCount A := by
  let r := fun a : Fin j => (observedFactor A R C z K hK hW j delta failure v draws (some a):ℝ)
  let q := (observedFactor A R C z K hK hW j delta failure v draws none:ℝ)
  have hr := observed_ratio_bounds A R C hC z hz K hK hW hB j delta failure hd hf v draws
  have hq := observed_correction_bounds A R C hC z K hK hW hB j hj delta failure hd hd1 hf v draws
  have hrlow : (1/2:ℝ)^j ≤ ∏ a,r a := by
    have hh := Finset.prod_le_prod₀ (s := Finset.univ)
      (fun _ _ => by norm_num : ∀ a : Fin j,a∈Finset.univ → (0:ℝ) ≤ 1/2)
      (fun a _ => (hr a).1)
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hh
  have hrup : (∏ a,r a) ≤ 1 := by
    have hh := Finset.prod_le_prod₀ (s := Finset.univ)
      (fun a _ => show (0:ℝ) ≤ r a from (by have h := (hr a).1; linarith)) (fun a _ => (hr a).2)
    simpa only [Finset.prod_const_one] using hh
  have hr0 : (0:ℝ) ≤ ∏ a,r a := Finset.prod_nonneg (fun a _ => by have h := (hr a).1; linarith)
  have hq0 : 0 ≤ q := by dsimp only [q]; linarith [hq.1]
  have hlow : (1/16:ℝ)*(1/2:ℝ)^j ≤ q*(∏ a,r a) :=
    mul_le_mul hq.1 hrlow (by positivity) hq0
  have hupp : q*(∏ a,r a) ≤ 8 := by
    calc
      _ ≤ 8*1 := mul_le_mul hq.2 hrup hr0 (by norm_num)
      _ = _ := by norm_num
  have hMf : (0:ℝ) ≤ assignmentCount A := Nat.cast_nonneg _
  have he : (estimateValue A R C z K hK hW j delta failure v draws:ℝ)=
      (assignmentCount A:ℝ)*(q*∏ a,r a) := by
    simp only [estimateValue,Rat.cast_mul,Rat.cast_natCast,Rat.cast_prod,Fintype.prod_option]
    rfl
  rw [he]
  constructor
  · have hh := mul_le_mul_of_nonneg_left hlow hMf
    nlinarith
  · have hh := mul_le_mul_of_nonneg_left hupp hMf
    nlinarith

theorem estimateValue_positive (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C)
    (delta failure : ℚ) (hd : 0 < delta) (hd1 : delta < 1) (hf : 0 < failure)
    (v : Grid (I := Fin (dimension A)) K) (draws : EstimatorInput A C K j delta failure) :
    0 < estimateValue A R C z K hK hW j delta failure v draws := by
  have hMf : (0:ℝ) < assignmentCount A := by exact_mod_cast assignmentCount_positive A
  have hh := (estimateValue_range A R C hC z hz K hK hW hB j hj delta failure hd hd1 hf v draws).1
  have hp : (0:ℝ) < (assignmentCount A:ℝ)*(1/2:ℝ)^j/16 := by positivity
  exact_mod_cast lt_of_lt_of_le hp hh

end

end ContingencyTables.RootedOracleDensity

end OAI
