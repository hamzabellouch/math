import OAI.Combinatorics.ContingencyTables.Rooted.ForestAffineProgram

namespace OAI

/-! # Exact rational assembly of the companion forest penalty

The natural root discrepancy and the finite list of tree affine forms
are combined by polynomial binary arithmetic to compute rationalD,
including the original maximum-forest cuts.
-/

namespace ContingencyTables.ForestPenaltyProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open CompanionFactorialApplication CompanionOracleDensity ForestAssignmentSplit GraphCompletionCounts
open ForestScaledPenalty
open scoped BigOperators Classical

abbrev Input := (ℕ×ℕ)×List ForestAffineProgram.Input

def rootFractionRealizer : Realizer (fun z : Input => (z.1.2,(1:ℕ))) :=
  pair (composition first second) (constant 1)

def scaleFractionRealizer : Realizer (fun z : Input => (z.1.1,(1:ℕ))) :=
  pair (composition first first) (constant 1)

def treeSum (z : Input) : TreeFraction.Fraction :=
  TreeFraction.sum (z.2.map ForestAffineProgram.evaluate)

def treeSumRealizer : Realizer treeSum :=
  composition (f := fun z : Input => z.2.map ForestAffineProgram.evaluate)
    (g := TreeFraction.sum)
    (composition second (map ForestAffineProgram.evaluateRealizer)) TreeFraction.sumRealizer

lemma polynomial_treeSum : PolynomialTime treeSumRealizer :=
  polynomial_composition (polynomial_composition polynomial_second
    (polynomial_map ForestAffineProgram.polynomial_evaluate)) TreeFraction.polynomial_sum

def penaltyCode (z : Input) : TreeFraction.Fraction :=
  TreeFraction.mul ((z.1.1,1),TreeFraction.add ((z.1.2,1),treeSum z))

def rootSumRealizer : Realizer (fun z : Input => TreeFraction.add ((z.1.2,1),treeSum z)) :=
  composition (f := fun z : Input => ((z.1.2,1),treeSum z)) (g := TreeFraction.add)
    (pair rootFractionRealizer treeSumRealizer) TreeFraction.addRealizer

lemma polynomial_rootSum : PolynomialTime rootSumRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
      (polynomial_constant 1)) polynomial_treeSum) TreeFraction.polynomial_add

def penaltyCodeRealizer : Realizer penaltyCode :=
  composition (f := fun z : Input => ((z.1.1,1),TreeFraction.add ((z.1.2,1),treeSum z)))
    (g := TreeFraction.mul)
    (pair scaleFractionRealizer rootSumRealizer)
    TreeFraction.mulRealizer

theorem polynomial_penaltyCode : PolynomialTime penaltyCodeRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_pair (polynomial_composition polynomial_first polynomial_first) (polynomial_constant 1))
    polynomial_rootSum) TreeFraction.polynomial_mul

lemma penaltyCode_value (z : Input) :
    TreeFraction.val (penaltyCode z)=(z.1.1:ℚ)*
      ((z.1.2:ℚ)+(z.2.map (fun t => TreeFraction.val (ForestAffineProgram.evaluate t))).sum) := by
  rw [penaltyCode,TreeFraction.mul_val,TreeFraction.add_val _ _ (show (1:ℕ)≠0 from Nat.one_ne_zero) (by
    exact (TreeFraction.sum_den _).ne')]
  rw [show TreeFraction.val (z.1.1,1)=(z.1.1:ℚ) by simp [TreeFraction.val],
    show TreeFraction.val (z.1.2,1)=(z.1.2:ℚ) by simp [TreeFraction.val]]
  rw [treeSum,TreeFraction.sum_val]
  · simp only [List.map_map,Function.comp_def]
  · intro f hf
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hf
    exact RationalIntervalProgram.intervalCode_denominator _


abbrev ExponentInput := (ℕ×ℕ)×Input

def weightedPenalty (z : ExponentInput) : TreeFraction.Fraction :=
  TreeFraction.mul (z.1,penaltyCode z.2)

def weightedPenaltyRealizer : Realizer weightedPenalty :=
  composition (f := fun z : ExponentInput => (z.1,penaltyCode z.2)) (g := TreeFraction.mul)
    (pair first (composition (f := fun z : ExponentInput => z.2) (g := penaltyCode)
      second penaltyCodeRealizer)) TreeFraction.mulRealizer

lemma polynomial_weightedPenalty : PolynomialTime weightedPenaltyRealizer :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition polynomial_second polynomial_penaltyCode)) TreeFraction.polynomial_mul

def exponentCode (z : ExponentInput) : ℕ := (weightedPenalty z).1/(weightedPenalty z).2

def exponentCodeRealizer : Realizer exponentCode :=
  composition (f := weightedPenalty) (g := fun f : TreeFraction.Fraction => f.1/f.2)
    weightedPenaltyRealizer quotient

theorem polynomial_exponentCode : PolynomialTime exponentCodeRealizer :=
  polynomial_composition polynomial_weightedPenalty polynomial_quotient

lemma exponentCode_value (z : ExponentInput) :
    exponentCode z=⌊(z.1.1:ℚ)/z.1.2*TreeFraction.val (penaltyCode z.2)⌋₊ := by
  have h := FractionAcceptanceProgram.fraction_threshold 0 (weightedPenalty z)
  simp only [FairBits.rationalThreshold,pow_zero,one_mul,Nat.mul_one] at h
  rw [exponentCode,←h,weightedPenalty,TreeFraction.mul_val]
  rfl

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

/-- This is the integral root part occurring in the source's exact
forest completion, before multiplying by the softening strength. -/
def rootCount (A : Instance I J) (x y : I → J → ℤ) : ℕ :=
  ∑ a : I⊕J,if ForestPenaltyApplication.rootFlag A.T a then
    (ForestRootPenalty.signedResidual A.small A.T A.r A.c x y 0 a).natAbs else 0

lemma rootCount_cast (A : Instance I J) (x y : I → J → ℤ) :
    (rootCount A x y:ℚ)=rationalRootConstant A x y := by
  unfold rootCount rationalRootConstant
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs
  · rw [←Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs]
  · exact Nat.cast_zero

variable {q t : ℕ}

def data (A : Instance I J) (C : ℕ) (z : View A → ℕ)
    (trees : Fin t ≃ TreeCell A.T) (free : Fin q ≃ FreeCell A.small A.T)
    (v : FreeCell A.small A.T → ℕ) : Input :=
  ((C,rootCount A (rowCounts A z) (columnCounts A z)),
    List.ofFn (fun i => ForestAffineProgram.forestData A C (trees i)
      (rowCounts A z) (columnCounts A z) free v))

/-- The compiled finite arithmetic computes the actual rational penalty;
this statement uses no oracle or approximate-evaluation premise. -/
theorem penaltyCode_data (A : Instance I J) (C : ℕ) (hC : 0<C) (z : View A → ℕ)
    (trees : Fin t ≃ TreeCell A.T) (free : Fin q ≃ FreeCell A.small A.T)
    (v : FreeCell A.small A.T → ℕ) :
    TreeFraction.val (penaltyCode (data A C z trees free v))=
      rationalD A C z (fun i => (v (index A i):ℚ)) := by
  rw [penaltyCode_value]
  simp only [data,List.map_ofFn,Function.comp_apply,List.sum_ofFn,rootCount_cast,
    ForestAffineProgram.evaluate_forest A C hC]
  unfold rationalD
  congr 2
  have hv : (fun f : FreeCell A.small A.T => (v (index A ((index A).symm f)):ℚ))=
      (fun f => (v f:ℚ)) := by
    funext f
    rw [Equiv.apply_symm_apply]
  rw [hv]
  exact Fintype.sum_equiv trees _ _ (fun _ => rfl)


theorem exponentCode_data (A : Instance I J) (C a : ℕ) (hC : 0<C) (z : View A → ℕ)
    (trees : Fin t ≃ TreeCell A.T) (free : Fin q ≃ FreeCell A.small A.T)
    (v : FreeCell A.small A.T → ℕ) :
    exponentCode ((a,rationalHeight A C),data A C z trees free v)=
      ⌊(a:ℚ)/rationalHeight A C*rationalD A C z (fun i => (v (index A i):ℚ))⌋₊ := by
  rw [exponentCode_value,penaltyCode_data A C hC]

end
end ContingencyTables.ForestPenaltyProgram

end OAI
