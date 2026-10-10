import OAI.Combinatorics.ContingencyTables.Counting.CompanionEstimatorAmplification
import OAI.Combinatorics.ContingencyTables.Counting.CompanionAnnealing

namespace OAI

/-! # The actual labelled-weight oracle used by the outer chain -/

namespace ContingencyTables.CompanionWeightOracle

open CompanionFactorialApplication CompanionOracleDensity GridBoundary LabelledFactorial TwoLiftStates
open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def profile (A : Instance I J) (S : Set (Labels A×Bool)) : View A → ℕ :=
  groupCount (group (labelCell A)) S

lemma profile_inBox (A : Instance I J) (S : Set (Labels A×Bool)) :
    BalancedBox.InBox (bounds A) (profile A S) := by
  rw [←label_capacity]
  exact SliceFactorial.groupCount_inBox _ _

def factorialNumerator (A : Instance I J) (S : Set (Labels A×Bool)) : ℕ :=
  ∏ u : View A, (profile A S u).factorial

def factorialDenominator (A : Instance I J) : ℕ :=
  ∏ s : SmallCell A, (A.b s.val.1 s.val.2).factorial

def factorialRatio (A : Instance I J) (S : Set (Labels A×Bool)) : ℚ :=
  (factorialNumerator A S:ℚ)/factorialDenominator A

lemma factorialRatio_positive (A : Instance I J) (S : Set (Labels A×Bool)) :
    0 < factorialRatio A S := by
  unfold factorialRatio factorialNumerator factorialDenominator
  positivity

lemma factorialRatio_cast (A : Instance I J) (S : Set (Labels A×Bool)) :
    (factorialRatio A S:ℝ)=
      FactorialSignatures.factorialProduct (profile A S)/CompanionFactorialApplication.denominator A := by
  simp only [factorialRatio,factorialNumerator,factorialDenominator,Rat.cast_div,Rat.cast_prod,
    Rat.cast_natCast,Nat.cast_prod,FactorialSignatures.factorialProduct,CompanionFactorialApplication.denominator,
    TwoLiftStates.denominator,label_width]

theorem weight_source (A : Instance I J) (C : ℕ) (hC : 0 < C) (j : ℕ)
    (S : Set (Labels A×Bool)) :
    CompanionAnnealing.weight A j S=
      h A ((j:ℝ)*C/height A C) (profile A S)*(factorialRatio A S:ℝ) := by
  rw [factorialRatio_cast]
  have he : (j:ℝ)*(C:ℝ)/height A C=(j:ℝ)/CompanionAnnealing.scale A := by
    simpa only [height,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,Nat.cast_add,Nat.cast_one] using
      CompanionAnnealing.source_parameter A C j hC
  rw [he]
  simp only [CompanionAnnealing.weight,CompanionFactorialApplication.f,firstLift,profile,mul_div_assoc]

abbrev WeightWord (A : Instance I J) (C K j : ℕ) (xi : ℚ) :=
  Fin (medianEstimatorBits A C K j xi xi) → Bool

def evaluate (A : Instance I J) (C : ℕ) (K : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (j : ℕ) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (S : Set (Labels A×Bool))
    (bits : WeightWord A C K j xi) : ℚ :=
  medianEstimate A C (profile A S) K hK hW j xi xi v bits*factorialRatio A S

/-- The relative-accuracy event describes the weight evaluator at
each labelled state. -/
def accurateCall (A : Instance I J) (C K j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (S : Set (Labels A×Bool))
    (bits : WeightWord A C K j xi) : Prop :=
  (1-(xi:ℝ))*CompanionAnnealing.weight A j S ≤ (evaluate A C K hK hW j xi v S bits:ℝ) ∧
    (evaluate A C K hK hW j xi v S bits:ℝ) ≤ (1+(xi:ℝ))*CompanionAnnealing.weight A j S

lemma evaluate_positive (A : Instance I J) (C : ℕ) (hC : 0 < C) (K : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (j : ℕ) (hj : j ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi < 1)
    (v : Grid (I := Fin (dimension A)) K) (S : Set (Labels A×Bool))
    (bits : WeightWord A C K j xi) : 0 < evaluate A C K hK hW j xi v S bits := by
  have hr := (medianEstimate_range A C hC (profile A S) (profile_inBox A S)
    K hK hW hB j hj xi xi hx0 hx1 v bits).1
  have hc : (0:ℝ) < assignmentCount A := by exact_mod_cast assignmentCount_positive A
  have hm : (0:ℚ) < medianEstimate A C (profile A S) K hK hW j xi xi v bits := by
    exact_mod_cast lt_of_lt_of_le (by positivity : (0:ℝ) < (assignmentCount A:ℝ)*(1/2:ℝ)^j/16) hr
  exact mul_pos hm (factorialRatio_positive A S)

/-- Every query at the actual labelled state uses a fresh bounded word.
Only PL and finite Cheeger remain in the evaluation guarantee. -/
theorem evaluate_success (A : Instance I J) (C : ℕ) (hC : 0 < C) (K : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (j : ℕ) (hj : j ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi < 1)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (S : Set (Labels A×Bool)) :
    1-(xi:ℝ) ≤ uniformAverage (fun bits : WeightWord A C K j xi =>
      if accurateCall A C K j hK hW xi v S bits then (1:ℝ) else 0) := by
  unfold accurateCall
  have hs := medianEstimate_success A C hC (profile A S) (profile_inBox A S)
    K hK hW hB j hj xi xi hx0 hx1 hx0 hPL hCheeger v
  apply hs.trans
  apply uniformAverage_mono
  intro bits
  by_cases hg : (1-(xi:ℝ))*h A ((j:ℝ)*C/height A C) (profile A S) ≤
      (medianEstimate A C (profile A S) K hK hW j xi xi v bits:ℝ) ∧
    (medianEstimate A C (profile A S) K hK hW j xi xi v bits:ℝ) ≤
      (1+(xi:ℝ))*h A ((j:ℝ)*C/height A C) (profile A S)
  · have hf : (0:ℝ) ≤ factorialRatio A S := by exact_mod_cast (factorialRatio_positive A S).le
    have hlo := mul_le_mul_of_nonneg_right hg.1 hf
    have hhi := mul_le_mul_of_nonneg_right hg.2 hf
    have ho : (1-(xi:ℝ))*CompanionAnnealing.weight A j S ≤ (evaluate A C K hK hW j xi v S bits:ℝ) ∧
        (evaluate A C K hK hW j xi v S bits:ℝ) ≤ (1+(xi:ℝ))*CompanionAnnealing.weight A j S := by
      rw [weight_source A C hC j S]
      simpa only [evaluate,Rat.cast_mul,mul_assoc] using And.intro hlo hhi
    simp only [hg,ho,le_refl]
  · simp only [hg,ite_false]
    split_ifs <;> norm_num

end

end ContingencyTables.CompanionWeightOracle

end OAI
