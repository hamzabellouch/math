import OAI.Combinatorics.ContingencyTables.Dense.DenseInteriorVolume
import OAI.Combinatorics.ContingencyTables.Dense.DenseChain

namespace OAI

/-!
# Feasible bins and exponent bounds for dense rejection

These bounds use the actual quotient widths and margin-derived penalty.
In particular, every bin containing a feasible point has weight one.
-/

namespace ContingencyTables.DenseAffine

open scoped BigOperators

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem densePenalty_change (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (x y : I × J → ℝ) (r : ℝ)
    (hr : 0 ≤ r) (hxy : ∀ p, |x p - y p| ≤ r) :
    |densePenalty R P d x - densePenalty R P d y| ≤ ((d : ℝ) / (d : ℝ) ^ 8) * r := by
  have hb := AffinePenalty.penalty_change
    (fun g => entryOffset (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g /
      cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g)
    (fun g p => entryCoeff (denseWidth R P d) g p /
      cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g)
    ((d : ℝ) / (d : ℝ) ^ 8) x y (1 / (d : ℝ) ^ 8) r (by positivity) hr
    (dense_normalized_coeff_bound R P d hd hR hP hRmax hPmax) hxy
  have hc : (Fintype.card (I × J) : ℝ) ≤ d := by exact_mod_cast hfree
  calc
    _ ≤ Fintype.card (I × J) * (1 / (d : ℝ) ^ 8) * r := hb
    _ ≤ (d : ℝ) * (1 / (d : ℝ) ^ 8) * r := by gcongr
    _ = _ := by ring

theorem densePenalty_cube_bound (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (x : I × J → ℝ) (hx : ∀ p, 0 ≤ x p ∧ x p ≤ 4 * (d : ℝ) ^ 8) :
    0 ≤ densePenalty R P d x ∧ densePenalty R P d x ≤ 4 * d := by
  obtain ⟨u, hu, hcube, _⟩ := dense_interior_exists R P d hd hR hP hdimR hdimP htotal
  have hxy (p : I × J) : |x p - u p| ≤ 4 * (d : ℝ) ^ 8 := by
    apply abs_le.mpr
    constructor <;> linarith [(hx p).1, (hx p).2, (hcube p).1, (hcube p).2,
      show (0 : ℝ) ≤ (d : ℝ) ^ 8 by positivity]
  have hb := densePenalty_change R P d hd hR hP hRmax hPmax hfree x u
    (4 * (d : ℝ) ^ 8) (by positivity) hxy
  rw [densePenalty_eq_zero_of_feasible R P d u hu, sub_zero] at hb
  have hd₀ : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have heq : ((d : ℝ) / (d : ℝ) ^ 8) * (4 * (d : ℝ) ^ 8) = 4 * d := by
    field_simp
  exact ⟨AffinePenalty.penalty_nonnegative _ _ _ _, (le_abs_self _).trans (hb.trans_eq heq)⟩

theorem densePenalty_corner_zero (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (v x : I × J → ℝ)
    (hx : Feasible R P d x) (hvx : ∀ p, |v p - x p| ≤ 1) :
    densePenalty R P d v = 0 := by
  apply le_antisymm
  · unfold densePenalty AffinePenalty.penalty
    apply Finset.sup'_le
    intro g _
    cases g with
    | none => exact le_rfl
    | some g =>
      change -AffinePenalty.affineValue _ _ v - (d : ℝ) / (d : ℝ) ^ 8 ≤ 0
      rw [← normalized_table_affine]
      change -normalizedEntry R P d v g - (d : ℝ) / (d : ℝ) ^ 8 ≤ 0
      have hb := normalizedEntry_change R P d hd hR hP hRmax hPmax hfree v x 1
        (by norm_num) hvx g
      have hnonneg : 0 ≤ normalizedEntry R P d x g :=
        div_nonneg (hx g.1 g.2) (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      have hl := (abs_le.mp hb).1
      linarith
  · exact AffinePenalty.penalty_nonnegative _ _ _ _

end

end ContingencyTables.DenseAffine

namespace ContingencyTables.GridBoundary

open scoped BigOperators

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q K : ℕ}

theorem denseGridSize_pos (d : ℕ) (hd : 14 ≤ d) : 1 ≤ 4 * d ^ 8 := by
  have hd₀ : 0 < d := by omega
  exact Nat.succ_le_of_lt (Nat.mul_pos (by decide) (pow_pos hd₀ _))

theorem denseBinWeight_eq_one (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q)
    (a : Grid (I := Fin q) K) (x : Fin q → ℝ) (hx : ClosedBin (corner a) x)
    (hfeas : DenseAffine.Feasible R P d (fun p => x (e p))) :
    denseBinWeight R P d e a = 1 := by
  have hz := DenseAffine.densePenalty_corner_zero R P d hd hR hP hRmax hPmax hfree
    (fun p => realCorner a (e p)) (fun p => x (e p)) hfeas (fun p => by
      change |(corner a (e p) : ℝ) - x (e p)| ≤ 1
      apply abs_le.mpr
      constructor <;> linarith [(hx (e p)).1, (hx (e p)).2])
  simp only [denseBinWeight, denseGridPenalty, DenseWeights.binWeight, hz, mul_zero,
    Int.floor_zero, Int.cast_zero, neg_zero, Real.rpow_zero]

theorem denseBinWeight_le_one (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (e : I × J ≃ Fin q) (a : Grid (I := Fin q) K) :
    denseBinWeight R P d e a ≤ 1 := by
  have hp : 0 ≤ denseGridPenalty R P d e (realCorner a) :=
    AffinePenalty.penalty_nonnegative _ _ _ _
  have hfloor : (0 : ℤ) ≤ ⌊(d : ℝ) ^ 4 * denseGridPenalty R P d e (realCorner a)⌋ :=
    Int.floor_nonneg.mpr (mul_nonneg (by positivity) hp)
  unfold denseBinWeight DenseWeights.binWeight
  calc
    _ ≤ (2 : ℝ) ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      have hf : (0 : ℝ) ≤ (⌊(d : ℝ) ^ 4 * denseGridPenalty R P d e (realCorner a)⌋ : ℤ) :=
        by exact_mod_cast hfloor
      linarith)
    _ = 1 := Real.rpow_zero _

theorem denseBinWeight_lower (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4 * d ^ 8)) :
    (2 : ℝ) ^ (-(4 * (d : ℝ) ^ 5)) ≤ denseBinWeight R P d e a := by
  have hcube (p : I × J) : 0 ≤ realCorner a (e p) ∧ realCorner a (e p) ≤ 4 * (d : ℝ) ^ 8 := by
    have hlo : (0 : ℤ) ≤ corner a (e p) := (a (e p)).property.1
    have hhi : corner a (e p) ≤ (4 * d ^ 8 : ℕ) - 1 := (a (e p)).property.2
    constructor
    · change (0 : ℝ) ≤ (corner a (e p) : ℝ)
      exact_mod_cast hlo
    · have hupper : corner a (e p) ≤ (4 * d ^ 8 : ℕ) := by
        omega
      change (corner a (e p) : ℝ) ≤ 4 * (d : ℝ) ^ 8
      exact_mod_cast hupper
  have hp := (DenseAffine.densePenalty_cube_bound R P d hd hR hP hRmax hPmax
    hdimR hdimP hfree htotal _ hcube).2
  have hf := Int.floor_le ((d : ℝ) ^ 4 * denseGridPenalty R P d e (realCorner a))
  have hm := mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ (d : ℝ) ^ 4 by positivity)
  change (d : ℝ) ^ 4 * denseGridPenalty R P d e (realCorner a) ≤ (d : ℝ) ^ 4 * (4 * d) at hm
  unfold denseBinWeight DenseWeights.binWeight
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  change denseGridPenalty R P d e (realCorner a) ≤ 4 * d at hp
  nlinarith [show (d : ℝ) ^ 4 * (4 * d) = 4 * (d : ℝ) ^ 5 by ring]

theorem grid_card (q K : ℕ) : Fintype.card (Grid (I := Fin q) K) = K ^ q := by
  have hc : Fintype.card (Set.Icc (0 : ℤ) ((K : ℤ) - 1)) = K := by
    have h := Int.card_fintype_Icc_of_le 0 ((K : ℤ) - 1)
      (show (0 : ℤ) ≤ (K : ℤ) - 1 + 1 by omega)
    omega
  simp only [Grid, Fintype.card_fun, Fintype.card_fin, hc]

theorem denseBinChain_pi_lower (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4 * d ^ 8)) :
    (2 : ℝ) ^ (-(4 * (d : ℝ) ^ 5)) / ((4 * (d : ℝ) ^ 8) ^ q) ≤
      (denseBinChain R P d hd hfree e (denseGridSize_pos d hd)).π a := by
  let : Nonempty (Grid (I := Fin q) (4 * d ^ 8)) := ⟨a⟩
  let w := denseBinWeight R P d e (K := 4 * d ^ 8)
  have hw : ∀ z, 0 < w z := fun z => DenseWeights.binWeight_pos _ _ _
  have hz : 0 < ∑ z, w z := Finset.sum_pos (fun z _ => hw z) Finset.univ_nonempty
  have hsum : (∑ z, w z) ≤ (4 * (d : ℝ) ^ 8) ^ q := by
    calc
      _ ≤ ∑ _z : Grid (I := Fin q) (4 * d ^ 8), (1 : ℝ) :=
        Finset.sum_le_sum (fun z _ => denseBinWeight_le_one R P d e z)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        grid_card, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
  change _ ≤ w a / (∑ z, w z)
  exact div_le_div₀ (hw a).le
    (denseBinWeight_lower R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal e a) hz hsum

end

end ContingencyTables.GridBoundary

end OAI
