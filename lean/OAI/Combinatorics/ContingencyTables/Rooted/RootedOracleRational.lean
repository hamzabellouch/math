import OAI.Combinatorics.ContingencyTables.Rooted.RootedOracleCorrection
import OAI.Combinatorics.ContingencyTables.Rooted.RootedPenaltyProgram

namespace OAI

/-! # The computed-root grid weights are exactly dyadic rational values -/

namespace ContingencyTables.RootedOracleDensity

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit GraphCompletionCounts GridBoundary
open CompanionOracleDensity (dimension index height rationalHeight naturalBin)

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def rationalD (A : Instance I J) (S : Selection A.T) (C : ℕ)
    (z : View A → ℕ) (v : Fin (dimension A) → ℚ) : ℚ :=
  RootedPenaltyProgram.rationalPenalty A S C (ForestScaledPenalty.rowCounts A z)
    (ForestScaledPenalty.columnCounts A z) (fun f => v ((index A).symm f))

theorem rationalD_cast (A : Instance I J) (S : Selection A.T) (C : ℕ)
    (z : View A → ℕ) (v : Fin (dimension A) → ℚ) :
    (rationalD A S C z v:ℝ)=D A S C z (fun i => (v i:ℝ)) := by
  rw [rationalD,RootedPenaltyProgram.rationalPenalty_cast]
  rfl

lemma rationalD_nonnegative (A : Instance I J) (S : Selection A.T) (C : ℕ)
    (z : View A → ℕ) (v : Fin (dimension A) → ℚ) : 0≤ rationalD A S C z v := by
  have hh := D_nonnegative A S C (Nat.cast_nonneg C) z (fun i => (v i:ℝ))
  rw [←rationalD_cast] at hh
  exact_mod_cast hh

noncomputable def gridExponent (A : Instance I J) (S : Selection A.T) (C a : ℕ)
    (z : View A → ℕ) {K : ℕ} (v : Grid (I := Fin (dimension A)) K) : ℕ :=
  ⌊(a:ℚ)/rationalHeight A C*rationalD A S C z (fun i => (corner v i:ℚ))⌋₊

theorem gridExponent_eq_floor (A : Instance I J) (S : Selection A.T) (C a : ℕ)
    (z : View A → ℕ) {K : ℕ} (v : Grid (I := Fin (dimension A)) K) :
    (gridExponent A S C a z v:ℤ)=⌊(a:ℝ)/height A C*D A S C z (realCorner v)⌋ := by
  have hn := mul_nonneg (div_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg (rationalHeight A C)))
    (rationalD_nonnegative A S C z (fun i => (corner v i:ℚ)))
  rw [gridExponent,Int.natCast_floor_eq_floor hn]
  have he : (((a:ℚ)/rationalHeight A C*rationalD A S C z (fun i => (corner v i:ℚ)):ℚ):ℝ)=
      (a:ℝ)/height A C*D A S C z (realCorner v) := by
    simp only [Rat.cast_mul,Rat.cast_div,Rat.cast_natCast,
      CompanionOracleDensity.rationalHeight_cast,rationalD_cast,Rat.cast_intCast]
    rfl
  rw [←he,Rat.floor_cast]

theorem gridWeight_eq_dyadic (A : Instance I J) (S : Selection A.T) (C a : ℕ)
    (z : View A → ℕ) {K : ℕ} (v : Grid (I := Fin (dimension A)) K) :
    gridWeight A S C a z v=1/(2:ℝ)^gridExponent A S C a z v := by
  unfold gridWeight V DenseWeights.binWeight
  rw [←gridExponent_eq_floor]
  simp only [Int.cast_natCast,Real.rpow_neg (by norm_num : (0:ℝ)≤2),Real.rpow_natCast,one_div]

noncomputable def rationalGridWeight (A : Instance I J) (S : Selection A.T) (C a : ℕ)
    (z : View A → ℕ) {K : ℕ} (v : Grid (I := Fin (dimension A)) K) : ℚ :=
  1/(2:ℚ)^gridExponent A S C a z v

theorem rationalGridWeight_cast (A : Instance I J) (S : Selection A.T) (C a : ℕ)
    (z : View A → ℕ) {K : ℕ} (v : Grid (I := Fin (dimension A)) K) :
    (rationalGridWeight A S C a z v:ℝ)=gridWeight A S C a z v := by
  rw [gridWeight_eq_dyadic]
  simp only [rationalGridWeight,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat]

theorem exponentCode_grid (A : Instance I J) (S : Selection A.T) (C a : ℕ) (hC : 0<C)
    (z : View A → ℕ) {nt nf K : ℕ} (trees : Fin nt ≃ TreeCell A.T)
    (free : Fin nf ≃ FreeCell A.small A.T) (v : Grid (I := Fin (dimension A)) K) :
    ForestPenaltyProgram.exponentCode ((a,rationalHeight A C),RootedPenaltyProgram.data A S C
      (ForestScaledPenalty.rowCounts A z) (ForestScaledPenalty.columnCounts A z)
      trees free (naturalBin A v))=gridExponent A S C a z v := by
  have he : (fun f : FreeCell A.small A.T => (naturalBin A v f:ℚ))=
      (fun f => (corner v ((index A).symm f):ℚ)) := by
    funext f
    exact_mod_cast CompanionOracleDensity.naturalBin_cast A v f
  rw [RootedPenaltyProgram.exponentCode_data A S C a hC]
  unfold gridExponent rationalD
  rw [he]

end ContingencyTables.RootedOracleDensity

end OAI
