import OAI.Combinatorics.ContingencyTables.Counting.CompanionOracleMixing
import Mathlib.Data.Rat.Floor

namespace OAI

/-! # Exact rational arithmetic for the companion evaluator's bin weights -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit ForestScaledPenalty
open ForestAffineCoefficients ForestRootPenalty GraphCompletionCounts GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def rationalIndicator (b : Bool) : ℚ := if b then 1 else 0

lemma rationalIndicator_cast (b : Bool) : (rationalIndicator b:ℝ)=ForestCut.indicator b := by
  cases b <;> norm_num [rationalIndicator,ForestCut.indicator]

def rationalSign (A : Instance I J) (t : TreeCell A.T) (a : I×J) : ℚ :=
  rationalIndicator (cutSide A t (.inl a.1))-rationalIndicator (cutSide A t (.inr a.2))

lemma rationalSign_cast (A : Instance I J) (t : TreeCell A.T) (a : I×J) :
    (rationalSign A t a:ℝ)=sign A t a := by
  simp only [rationalSign,Rat.cast_sub,rationalIndicator_cast,sign]

def rationalCoefficient (A : Instance I J) (t : TreeCell A.T) (a : I×J) : ℚ :=
  if A.small a.1 a.2=false ∧ ¬A.T.Adj (.inl a.1) (.inr a.2)
  then -rationalSign A t a/rationalSign A t t.val else 0

lemma rationalCoefficient_cast (A : Instance I J) (t : TreeCell A.T) (a : I×J) :
    (rationalCoefficient A t a:ℝ)=coefficient A t a := by
  unfold rationalCoefficient coefficient
  split_ifs <;> simp only [Rat.cast_div,Rat.cast_neg,rationalSign_cast,Rat.cast_zero]

def rationalSmallContribution (A : Instance I J) (t : TreeCell A.T)
    (x q : I → J → ℤ) : ℚ :=
  ∑ a : I×J,if A.small a.1 a.2 then
    rationalIndicator (cutSide A t (.inl a.1))*((x a.1 a.2:ℚ)-A.X a.1 a.2)-
      rationalIndicator (cutSide A t (.inr a.2))*((q a.1 a.2:ℚ)-A.X a.1 a.2) else 0

lemma rationalSmallContribution_cast (A : Instance I J) (t : TreeCell A.T)
    (x q : I → J → ℤ) :
    (rationalSmallContribution A t x q:ℝ)=
      smallContribution A t (fun i j => (x i j:ℝ)) (fun i j => (q i j:ℝ)) := by
  unfold rationalSmallContribution smallContribution
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp only [Rat.cast_sub,Rat.cast_mul,rationalIndicator_cast,
    Rat.cast_intCast,Rat.cast_zero]

def rationalOffset (A : Instance I J) (t : TreeCell A.T) (x q : I → J → ℤ) : ℚ :=
  A.X t.val.1 t.val.2-rationalSmallContribution A t x q/rationalSign A t t.val-
    ∑ a : I×J,rationalCoefficient A t a*(A.X a.1 a.2:ℚ)

lemma rationalOffset_cast (A : Instance I J) (t : TreeCell A.T) (x q : I → J → ℤ) :
    (rationalOffset A t x q:ℝ)=
      offset A t (fun i j => (x i j:ℝ)) (fun i j => (q i j:ℝ)) := by
  simp only [rationalOffset,offset,Rat.cast_sub,Rat.cast_div,Rat.cast_intCast,
    Rat.cast_sum,Rat.cast_mul,rationalCoefficient_cast,rationalSign_cast,
    rationalSmallContribution_cast]

def rationalBinWidth (A : Instance I J) (C : ℕ) : ℕ := 16*C*A.d^2

def rationalHeight (A : Instance I J) (C : ℕ) : ℕ := 10*C*A.d^2*(A.W+1)

lemma rationalBinWidth_cast (A : Instance I J) (C : ℕ) :
    (rationalBinWidth A C:ℝ)=binWidth A C := by
  simp only [rationalBinWidth,binWidth,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]

lemma rationalHeight_cast (A : Instance I J) (C : ℕ) :
    (rationalHeight A C:ℝ)=height A C := by
  simp only [rationalHeight,height,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,Nat.cast_add,Nat.cast_one]

def rationalScaledTree (A : Instance I J) (C : ℕ) (x q : I → J → ℤ)
    (v : FreeCell A.small A.T → ℚ) (t : TreeCell A.T) : ℚ :=
  rationalOffset A t x q/(A.b t.val.1 t.val.2:ℚ)+
    ∑ f : FreeCell A.small A.T,
      (rationalCoefficient A t f.val*((A.b f.val.1 f.val.2:ℚ)+1)/rationalBinWidth A C/
        (A.b t.val.1 t.val.2:ℚ))*v f

lemma rationalScaledTree_cast (A : Instance I J) (C : ℕ) (x q : I → J → ℤ)
    (v : FreeCell A.small A.T → ℚ) (t : TreeCell A.T) :
    (rationalScaledTree A C x q v t:ℝ)=
      scaledTree A (binWidth A C) x q (fun f => (v f:ℝ)) t := by
  simp only [rationalScaledTree,scaledTree,AffinePenalty.affineValue,normalizedOffset,
    normalizedCoefficient,Rat.cast_add,Rat.cast_div,Rat.cast_mul,Rat.cast_sum,
    Rat.cast_natCast,Rat.cast_one,rationalOffset_cast,rationalCoefficient_cast,rationalBinWidth_cast]

def rationalRootConstant (A : Instance I J) (x q : I → J → ℤ) : ℚ :=
  ∑ a,if ForestPenaltyApplication.rootFlag A.T a then
    |(signedResidual A.small A.T A.r A.c x q 0 a:ℚ)| else 0

lemma rationalRootConstant_cast (A : Instance I J) (x q : I → J → ℤ) :
    (rationalRootConstant A x q:ℝ)=rootConstant A x q := by
  unfold rationalRootConstant rootConstant
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp only [Rat.cast_abs,Rat.cast_intCast,Rat.cast_zero]

def rationalD (A : Instance I J) (C : ℕ) (z : View A → ℕ)
    (v : Fin (dimension A) → ℚ) : ℚ :=
  C*(rationalRootConstant A (rowCounts A z) (columnCounts A z)+
    ∑ t : TreeCell A.T,max 0 (max
      (-rationalScaledTree A C (rowCounts A z) (columnCounts A z) (fun f => v ((index A).symm f)) t)
      (rationalScaledTree A C (rowCounts A z) (columnCounts A z) (fun f => v ((index A).symm f)) t-1)))

/-- The rational calculation is termwise equal to the geometric density
penalty; it does not use an approximation or enumerate free assignments. -/
theorem rationalD_cast (A : Instance I J) (C : ℕ) (z : View A → ℕ)
    (v : Fin (dimension A) → ℚ) :
    (rationalD A C z v:ℝ)=D A C z (fun i => (v i:ℝ)) := by
  simp only [rationalD,D,penalty,intervalCost,Rat.cast_mul,Rat.cast_natCast,
    Rat.cast_add,Rat.cast_sum,rationalRootConstant_cast,Rat.cast_max,Rat.cast_zero,
    Rat.cast_neg,Rat.cast_sub,Rat.cast_one,rationalScaledTree_cast]
  rfl

lemma rationalD_nonnegative (A : Instance I J) (C : ℕ) (z : View A → ℕ)
    (v : Fin (dimension A) → ℚ) : 0 ≤ rationalD A C z v := by
  have hh := penalty_nonnegative A (C:ℝ) (binWidth A C) (Nat.cast_nonneg _)
    (rowCounts A z) (columnCounts A z) (pull A (fun i => (v i:ℝ)))
  change 0 ≤ D A C z (fun i => (v i:ℝ)) at hh
  rw [←rationalD_cast] at hh
  exact_mod_cast hh

def gridExponent (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) : ℕ :=
  ⌊(a:ℚ)/rationalHeight A C*rationalD A C z (fun i => (corner v i:ℚ))⌋₊

theorem gridExponent_eq_floor (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) :
    (gridExponent A C a z v:ℤ)=⌊(a:ℝ)/height A C*D A C z (realCorner v)⌋ := by
  have hn := mul_nonneg (div_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg (rationalHeight A C)))
    (rationalD_nonnegative A C z (fun i => (corner v i:ℚ)))
  rw [gridExponent,Int.natCast_floor_eq_floor hn]
  have he : (((a:ℚ)/rationalHeight A C*rationalD A C z (fun i => (corner v i:ℚ)):ℚ):ℝ)=
      (a:ℝ)/height A C*D A C z (realCorner v) := by
    simp only [Rat.cast_mul,Rat.cast_div,Rat.cast_natCast,rationalHeight_cast,rationalD_cast,
      Rat.cast_intCast]
    rfl
  rw [←he,Rat.floor_cast]

theorem gridWeight_eq_dyadic (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) :
    gridWeight A C a z v=1/(2:ℝ)^gridExponent A C a z v := by
  unfold gridWeight V DenseWeights.binWeight
  rw [←gridExponent_eq_floor]
  simp only [Int.cast_natCast,Real.rpow_neg (by norm_num : (0:ℝ)≤2),Real.rpow_natCast,one_div]

theorem gridExponent_upper (A : Instance I J) (C a : ℕ) (hC : 0 < C)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hKB : (K:ℝ) ≤ binWidth A C) (v : Grid (I := Fin (dimension A)) K) :
    gridExponent A C a z v ≤ a := by
  have hCR : (0:ℝ) < C := by exact_mod_cast hC
  have hD := D_bounds A C hCR z hz (realCorner v) (by
    intro i
    constructor
    · change (0:ℝ) ≤ ((v i).val:ℝ)
      exact_mod_cast (v i).property.1
    · have hh : (realCorner v i:ℝ) ≤ K := by
        change ((v i).val:ℝ) ≤ K
        exact_mod_cast (show (v i).val ≤ (K:ℤ) by have hh := (v i).property.2; omega)
      exact hh.trans hKB)
  have hH := height_positive A C hCR
  have hbound : (a:ℝ)/height A C*D A C z (realCorner v) ≤ a := by
    calc
      _ ≤ (a:ℝ)/height A C*height A C :=
        mul_le_mul_of_nonneg_left hD.2 (div_nonneg (Nat.cast_nonneg _) hH.le)
      _ = _ := div_mul_cancel₀ _ hH.ne'
  have he := gridExponent_eq_floor A C a z v
  have hh := (Int.floor_le ((a:ℝ)/height A C*D A C z (realCorner v))).trans hbound
  rw [←he] at hh
  exact_mod_cast hh

def rationalGridWeight (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) : ℚ :=
  1/(2:ℚ)^gridExponent A C a z v

theorem rationalGridWeight_cast (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) :
    (rationalGridWeight A C a z v:ℝ)=gridWeight A C a z v := by
  rw [gridWeight_eq_dyadic]
  simp only [rationalGridWeight,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat]

lemma rationalGridWeight_positive (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) : 0 < rationalGridWeight A C a z v := by
  unfold rationalGridWeight
  positivity

end

end ContingencyTables.CompanionOracleDensity

end OAI
