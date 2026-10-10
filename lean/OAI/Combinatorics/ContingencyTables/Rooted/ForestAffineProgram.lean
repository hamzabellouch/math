import OAI.Combinatorics.ContingencyTables.Rooted.ForestIntegerEvaluation
import OAI.Combinatorics.MatchingCount.Complexity.TreePolynomialSums

namespace OAI

/-! # Binary list evaluation of the forest's signed affine numerators

Each coefficient is stored by its nonnegative and nonpositive parts.
The program performs two finite product sums and passes their difference
to the proved interval-cost routine. Large capacities are never iterated.
-/

namespace ContingencyTables.ForestAffineProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators Classical

abbrev Term := (ℕ×ℕ)×ℕ
abbrev Input := ((ℕ×ℕ)×List Term)×ℕ

def positiveTerm (z : Term) : ℕ := z.1.1*z.2
def negativeTerm (z : Term) : ℕ := z.1.2*z.2

def positiveTermRealizer : Realizer positiveTerm :=
  composition (f := fun z : Term => (z.1.1,z.2)) (g := fun z : ℕ×ℕ => z.1*z.2)
    (pair (composition first first) second) multiply

def negativeTermRealizer : Realizer negativeTerm :=
  composition (f := fun z : Term => (z.1.2,z.2)) (g := fun z : ℕ×ℕ => z.1*z.2)
    (pair (composition first second) second) multiply

lemma polynomial_positiveTerm : PolynomialTime positiveTermRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_multiply

lemma polynomial_negativeTerm : PolynomialTime negativeTermRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_second) polynomial_second) polynomial_multiply

def positiveSumRealizer : Realizer (fun xs : List Term => (xs.map positiveTerm).sum) :=
  composition (map positiveTermRealizer) listSum

def negativeSumRealizer : Realizer (fun xs : List Term => (xs.map negativeTerm).sum) :=
  composition (map negativeTermRealizer) listSum

lemma polynomial_positiveSum : PolynomialTime positiveSumRealizer :=
  polynomial_composition (polynomial_map polynomial_positiveTerm) polynomial_listSum

lemma polynomial_negativeSum : PolynomialTime negativeSumRealizer :=
  polynomial_composition (polynomial_map polynomial_negativeTerm) polynomial_listSum

def parts (z : Input) : ℕ×ℕ :=
  (z.1.1.1+(z.1.2.map positiveTerm).sum,z.1.1.2+(z.1.2.map negativeTerm).sum)

def partsRealizer : Realizer parts :=
  pair
    (composition (pair (composition (composition first first) first)
      (composition (composition first second) positiveSumRealizer)) add)
    (composition (pair (composition (composition first first) second)
      (composition (composition first second) negativeSumRealizer)) add)

lemma polynomial_parts : PolynomialTime partsRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
        polynomial_positiveSum)) polynomial_add)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
        polynomial_negativeSum)) polynomial_add)

def evaluate (z : Input) : TreeFraction.Fraction :=
  RationalIntervalProgram.intervalCode (parts z,z.2)

def evaluateRealizer : Realizer evaluate :=
  composition (f := fun z : Input => (parts z,z.2)) (g := RationalIntervalProgram.intervalCode)
    (pair partsRealizer second) RationalIntervalProgram.intervalCodeRealizer

theorem polynomial_evaluate : PolynomialTime evaluateRealizer :=
  polynomial_composition (polynomial_pair polynomial_parts polynomial_second)
    RationalIntervalProgram.polynomial_intervalCode

def signedParts (z : ℤ) : ℕ×ℕ := (z.toNat,(-z).toNat)

lemma signedParts_sub (z : ℤ) : ((signedParts z).1:ℤ)-(signedParts z).2=z := by
  change (z.toNat:ℤ)-((-z).toNat:ℤ)=z
  omega

noncomputable section
variable {q : ℕ}

def data (offset : ℤ) (coefficient : Fin q → ℤ) (v : Fin q → ℕ) (den : ℕ) : Input :=
  ((signedParts offset,List.ofFn (fun i => (signedParts (coefficient i),v i))),den)

lemma parts_data (offset : ℤ) (coefficient : Fin q → ℤ) (v : Fin q → ℕ) (den : ℕ) :
    ((parts (data offset coefficient v den)).1:ℤ)-(parts (data offset coefficient v den)).2=
      offset+∑ i,coefficient i*(v i:ℤ) := by
  simp only [parts,data,List.map_ofFn,Function.comp_apply,positiveTerm,negativeTerm,
    List.sum_ofFn,Nat.cast_add,Nat.cast_sum,Nat.cast_mul]
  rw [add_sub_add_comm,←Finset.sum_sub_distrib,signedParts_sub]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [←sub_mul,signedParts_sub]

/-- All signs and products in an affine tree term are executed in
binary; the resulting fraction is its exact interval penalty. -/
theorem evaluate_data (offset : ℤ) (coefficient : Fin q → ℤ) (v : Fin q → ℕ)
    (den : ℕ) (hd : 0<den) :
    TreeFraction.val (evaluate (data offset coefficient v den))=
      max 0 (max (-(((offset:ℚ)+∑ i,(coefficient i:ℚ)*(v i:ℚ))/den))
        (((offset:ℚ)+∑ i,(coefficient i:ℚ)*(v i:ℚ))/den-1)) := by
  have he : ((parts (data offset coefficient v den)).1:ℚ)-
      (parts (data offset coefficient v den)).2=
      (offset:ℚ)+∑ i,(coefficient i:ℚ)*(v i:ℚ) := by
    exact_mod_cast parts_data offset coefficient v den
  calc
    _ = max 0 (max (-((((parts (data offset coefficient v den)).1:ℚ)-
          (parts (data offset coefficient v den)).2)/den))
        ((((parts (data offset coefficient v den)).1:ℚ)-
          (parts (data offset coefficient v den)).2)/den-1)) :=
      RationalIntervalProgram.intervalCode_value _ _ _ hd
    _ = _ := by rw [he]


open CompanionFactorialApplication ForestAssignmentSplit CompanionOracleDensity GraphCompletionCounts
open ForestIntegerEvaluation

variable {I J : Type*} [Fintype I] [Fintype J]

def forestData (A : Instance I J) (C : ℕ) (t : TreeCell A.T)
    (x y : I → J → ℤ) (e : Fin q ≃ FreeCell A.small A.T)
    (v : FreeCell A.small A.T → ℕ) : Input :=
  data ((rationalBinWidth A C:ℤ)*ForestIntegerEvaluation.offset A t x y)
    (fun i => ForestIntegerEvaluation.coefficient A t (e i).val*
      ((A.b (e i).val.1 (e i).val.2:ℤ)+1))
    (fun i => v (e i)) (rationalBinWidth A C*A.b t.val.1 t.val.2)

/-- This input is the literal cut-derived affine form of the manuscript.
The executable value is its exact contribution to the softened penalty. -/
theorem evaluate_forest (A : Instance I J) (C : ℕ) (hC : 0<C) (t : TreeCell A.T)
    (x y : I → J → ℤ) (e : Fin q ≃ FreeCell A.small A.T)
    (v : FreeCell A.small A.T → ℕ) :
    TreeFraction.val (evaluate (forestData A C t x y e v))=
      max 0 (max (-rationalScaledTree A C x y (fun f => (v f:ℚ)) t)
        (rationalScaledTree A C x y (fun f => (v f:ℚ)) t-1)) := by
  have hB : 0<rationalBinWidth A C := by
    unfold rationalBinWidth
    exact Nat.mul_pos (Nat.mul_pos (by decide) hC)
      (pow_pos (lt_of_lt_of_le Nat.zero_lt_one A.hd) _)
  have ht := (A.hlarge _ _ (A.hTG t.property)).2
  have hd := Nat.mul_pos hB ht
  have hn : (((rationalBinWidth A C:ℤ)*ForestIntegerEvaluation.offset A t x y:ℤ):ℚ)+
      ∑ i : Fin q,
        ((ForestIntegerEvaluation.coefficient A t (e i).val*
          ((A.b (e i).val.1 (e i).val.2:ℤ)+1):ℤ):ℚ)*(v (e i):ℚ)=
      (ForestIntegerEvaluation.numerator A C t x y v:ℚ) := by
    simp only [ForestIntegerEvaluation.numerator,Int.cast_add,Int.cast_mul,Int.cast_natCast,
      Int.cast_one,Int.cast_sum]
    congr 1
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  unfold forestData
  rw [evaluate_data _ _ _ _ hd,hn,Nat.cast_mul,ForestIntegerEvaluation.numerator_div A C hC]

end
end ContingencyTables.ForestAffineProgram

end OAI
