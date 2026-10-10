import OAI.Combinatorics.ContingencyTables.Dense.DenseTrialAcceptance
import Mathlib.Data.Rat.Floor

namespace OAI

/-! # Exact rational evaluation of the dense bin exponent

Only integer completion, rational comparison and division are needed to
compute a bin's weight exponent. The real penalty used in the geometric
proof is exactly the cast of this finite rational maximum.
-/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical

variable {I J : Type*} [Fintype I] [Fintype J]
variable {q K : ℕ}

def cornerFree (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) K) : I × J → ℕ :=
  fun p => integerWidth R P d p * (corner a (e p)).toNat

omit [Fintype I] [Fintype J] in
theorem cornerFree_cast (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) K) (p : I × J) :
    (cornerFree R P d e a p : ℝ) =
      DenseAffine.denseWidth R P d p.1 p.2 * realCorner a (e p) := by
  have hc : (((corner a (e p)).toNat : ℕ) : ℝ) = (corner a (e p) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (a (e p)).property.1
  simp only [cornerFree, Nat.cast_mul, hc]
  rfl

theorem corner_integerTable_cast (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) K) (i : Option I) (j : Option J) :
    (DenseAffine.integerTable R P (cornerFree R P d e a) i j : ℝ) =
      DenseAffine.table (fun i => (R i : ℝ)) (fun j => (P j : ℝ))
        (DenseAffine.denseWidth R P d) (fun p => realCorner a (e p)) i j := by
  rw [DenseAffine.integerTable_cast]
  cases i <;> cases j <;>
    simp only [DenseAffine.table, one_mul, cornerFree_cast]

def rationalComponent (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) K) :
    Option (Option I × Option J) → ℚ
  | none => 0
  | some g => -(DenseAffine.integerTable R P (cornerFree R P d e a) g.1 g.2 : ℚ) /
      ((min (R g.1) (P g.2) : ℕ) : ℚ) - (d : ℚ) / (d : ℚ) ^ 8

def rationalPenalty (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) K) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty (rationalComponent R P d e a)

theorem rationalPenalty_nonnegative (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) K) : 0 ≤ rationalPenalty R P d e a :=
  Finset.le_sup' (rationalComponent R P d e a) (Finset.mem_univ none)

variable [DecidableEq I] [DecidableEq J]

theorem rationalComponent_cast (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) K) (g : Option (Option I × Option J)) :
    (rationalComponent R P d e a g : ℝ) =
      AffinePenalty.component
        (fun g => DenseAffine.entryOffset (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g /
          DenseAffine.cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g)
        (fun g p => DenseAffine.entryCoeff (DenseAffine.denseWidth R P d) g p /
          DenseAffine.cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g)
        ((d : ℝ) / (d : ℝ) ^ 8) g (fun p => realCorner a (e p)) := by
  cases g with
  | none => simp only [rationalComponent, Rat.cast_zero, AffinePenalty.component]
  | some g =>
    simp only [rationalComponent, Rat.cast_sub, Rat.cast_div, Rat.cast_neg,
      Rat.cast_intCast, Rat.cast_natCast, Rat.cast_pow, AffinePenalty.component,
      Nat.cast_min, Rat.cast_min, neg_div]
    rw [corner_integerTable_cast]
    change -(_ / DenseAffine.cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g) - _ = _
    rw [DenseAffine.normalized_table_affine]

theorem rationalPenalty_cast (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) K) :
    (rationalPenalty R P d e a : ℝ) = denseGridPenalty R P d e (realCorner a) := by
  unfold rationalPenalty denseGridPenalty DenseAffine.densePenalty AffinePenalty.penalty
  rw [Finset.apply_sup'_eq_sup'_comp _ (fun x : ℚ => (x : ℝ))
    (fun x y => Rat.cast_max x y)]
  apply Finset.sup'_congr Finset.univ_nonempty rfl
  intro g _
  exact rationalComponent_cast R P d e a g

def denseExponent (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) K) : ℕ :=
  ⌊(d : ℚ) ^ 4 * rationalPenalty R P d e a⌋₊

theorem denseExponent_eq_floor (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) K) :
    (denseExponent R P d e a : ℤ) =
      ⌊(d : ℝ) ^ 4 * denseGridPenalty R P d e (realCorner a)⌋ := by
  have hp := rationalPenalty_nonnegative R P d e a
  rw [denseExponent, Int.natCast_floor_eq_floor (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hp)]
  have hcast : (((d : ℚ) ^ 4 * rationalPenalty R P d e a : ℚ) : ℝ) =
      (d : ℝ) ^ 4 * denseGridPenalty R P d e (realCorner a) := by
    simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, rationalPenalty_cast]
  rw [← hcast, Rat.floor_cast]

theorem denseBinWeight_eq_dyadic (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) K) :
    denseBinWeight R P d e a = 1 / (2 : ℝ) ^ denseExponent R P d e a := by
  unfold denseBinWeight DenseWeights.binWeight
  rw [← denseExponent_eq_floor]
  simp only [Int.cast_natCast, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_natCast, one_div]

end ContingencyTables.GridBoundary

end OAI
