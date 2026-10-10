import OAI.Combinatorics.ContingencyTables.Machines.BinaryContraction

namespace OAI

/-!
# Factorial congruence for the two binary lifts

The integer-to-binary signature transfer in paper 200-02,
Lemma `lem:binary-signatures`. Coordinates with zero remaining copies
are allowed; a single remaining copy gives an invalid repeated removal.
The copy matrix is proved to be dominated by the integer form compressed
to group means. The difference is the nonnegative within-group variance.
-/

namespace ContingencyTables.FactorialSignatures

open scoped BigOperators Classical Matrix
open LinearMap (BilinForm)
open CommonBasesFPRAS

/-- Domination by a compressed one-positive form preserves the signature.
This is the precise group-mean argument, including forms with no positive direction. -/
theorem onePositive_of_dominated_compression
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (B : BilinForm ℝ V) (C : BilinForm ℝ W) (L : W →ₗ[ℝ] V)
    (hsymm : ∀ x y, C x y = C y x) (hsig : OnePositiveDirection B)
    (hdom : ∀ v, C v v ≤ B (L v) (L v)) : OnePositiveDirection C := by
  by_cases hpos : ∃ u, 0 < C u u
  · obtain ⟨u, hu⟩ := hpos
    apply onePositiveDirection_of_kernel C hsymm ((B (L u)).comp L)
    intro v hv
    exact (hdom v).trans (hsig (L u) (lt_of_lt_of_le hu (hdom u)) (L v) hv)
  · intro u hu
    exact False.elim (hpos ⟨u, hu⟩)

variable {G : Type*} [Fintype G] [DecidableEq G]

abbrev Copies (n : G → ℕ) := (u : G) × Fin (n u)

noncomputable def groupAverage (n : G → ℕ) : (Copies n → ℝ) →ₗ[ℝ] (G → ℝ) where
  toFun x u := (∑ i : Fin (n u), x ⟨u, i⟩) / n u
  map_add' x y := by ext u; simp [Finset.sum_add_distrib, add_div]
  map_smul' a x := by
    ext u
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_div_assoc, RingHom.id_apply]

def groupIndicator (n : G → ℕ) (u : G) (i : Copies n) : ℝ := if i.1 = u then 1 else 0

def groupOuter (n : G → ℕ) (u : G) : Matrix (Copies n) (Copies n) ℝ :=
  fun i j => groupIndicator n u i * groupIndicator n u j

noncomputable def withinCoefficient (n : G → ℕ) (H : Matrix G G ℝ) (c : ℝ) (u : G) : ℝ :=
  c * H u u / ((n u : ℝ) * (n u - 1 : ℕ))

noncomputable def normalizedMatrix (n : G → ℕ) (H : Matrix G G ℝ) (c : ℝ) :
    Matrix (Copies n) (Copies n) ℝ :=
  fun i j => c * H i.1 j.1 / ((n i.1 : ℝ) * n j.1)

noncomputable def scaledPullback (n : G → ℕ) (H : Matrix G G ℝ) :
    Matrix (Copies n) (Copies n) ℝ :=
  fun i j => (1 / (n i.1 : ℝ)) * H i.1 j.1 * (1 / (n j.1 : ℝ))

/-- Exact normalized copy matrix, including the within-group diagonal correction. -/
noncomputable def copyMatrix (n : G → ℕ) (H : Matrix G G ℝ) (c : ℝ) :
    Matrix (Copies n) (Copies n) ℝ :=
  normalizedMatrix n H c +
    ∑ u, (withinCoefficient n H c u / n u) • groupOuter n u -
      Matrix.diagonal (fun i : Copies n => withinCoefficient n H c i.1)

lemma grouped_form (n : G → ℕ) (H : Matrix G G ℝ) (x y : Copies n → ℝ) :
    (H.submatrix Sigma.fst Sigma.fst).toBilin' x y =
      H.toBilin' (fun u => ∑ i : Fin (n u), x ⟨u, i⟩)
        (fun u => ∑ i : Fin (n u), y ⟨u, i⟩) := by
  simp only [Matrix.toBilin'_apply, Matrix.submatrix_apply, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, ← Finset.sum_mul]

lemma groupOuter_form (n : G → ℕ) (u : G) (x y : Copies n → ℝ) :
    (groupOuter n u).toBilin' x y =
      (∑ i : Fin (n u), x ⟨u, i⟩) * ∑ i : Fin (n u), y ⟨u, i⟩ := by
  simp only [Matrix.toBilin'_apply, groupOuter, groupIndicator, Fintype.sum_sigma]
  simp [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma normalized_form (n : G → ℕ) (H : Matrix G G ℝ) (c : ℝ) (x y : Copies n → ℝ) :
    (normalizedMatrix n H c).toBilin' x y =
      c * H.toBilin' (groupAverage n x) (groupAverage n y) := by
  have heq : normalizedMatrix n H c = c • scaledPullback n H := by
    ext i j
    simp only [normalizedMatrix, scaledPullback, Matrix.smul_apply, smul_eq_mul,
      div_mul_eq_div_div]
    ring
  rw [heq]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  congr 1
  have hg := grouped_form n H (fun i => x i / n i.1) (fun i => y i / n i.1)
  convert hg using 1
  · rw [Matrix.toBilin'_apply, Matrix.toBilin'_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [Matrix.submatrix_apply, scaledPullback]
    ring
  · congr 1 <;> ext u <;> simp [groupAverage, Finset.sum_div]

lemma diagonal_form (n : G → ℕ) (d x : Copies n → ℝ) :
    (Matrix.diagonal d).toBilin' x x = ∑ i, d i * x i * x i := by
  rw [Matrix.toBilin'_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.diagonal_apply, mul_ite, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-- The factorial copy form equals the integer form on group averages
minus the sum of within-group variances with their actual coefficients. -/
theorem copyMatrix_form (n : G → ℕ) (H : Matrix G G ℝ) (c : ℝ) (x : Copies n → ℝ) :
    (copyMatrix n H c).toBilin' x x =
      c * H.toBilin' (groupAverage n x) (groupAverage n x) -
        ∑ u, withinCoefficient n H c u *
          ((∑ i : Fin (n u), x ⟨u, i⟩ ^ 2) -
            (∑ i : Fin (n u), x ⟨u, i⟩) ^ 2 / n u) := by
  simp only [copyMatrix, map_sub, map_add, map_sum, map_smul,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, normalized_form, groupOuter_form,
    diagonal_form]
  simp only [Fintype.sum_sigma]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  have halg (a b d r : ℝ) : a * (b - d ^ 2 / r) = a * b - a / r * (d * d) := by ring
  simp_rw [halg, Finset.sum_sub_distrib, pow_two]
  ring

omit [Fintype G] [DecidableEq G] in
lemma within_variance_nonnegative (n : ℕ) (x : Fin n → ℝ) :
    0 ≤ (∑ i, x i ^ 2) - (∑ i, x i) ^ 2 / n := by
  by_cases hn : n = 0
  · subst n
    simp
  have hnr : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin n => (1 : ℝ)) x
  have hh : (∑ i, x i) ^ 2 ≤ (n : ℝ) * ∑ i, x i ^ 2 := by simpa using hcs
  exact sub_nonneg.mpr ((div_le_iff₀ hnr).mpr (by nlinarith [hh]))

/-- Raw integer signatures imply signatures of the actual copy matrix.
Zero groups are harmless and single-copy groups require no division argument. -/
theorem copyMatrix_onePositive (n : G → ℕ) (H : Matrix G G ℝ) (c : ℝ)
    (hc : 0 < c) (hH : ∀ u v, H u v = H v u)
    (hsig : OnePositiveDirection H.toBilin') (hdiag : ∀ u, 0 ≤ H u u) :
    OnePositiveDirection (copyMatrix n H c).toBilin' := by
  have hcSig : OnePositiveDirection (c • H.toBilin') := by
    intro u hu v hv
    simp only [LinearMap.smul_apply, smul_eq_mul] at hu hv ⊢
    have hu' : 0 < H.toBilin' u u := pos_of_mul_pos_right hu hc.le
    have hv' : H.toBilin' u v = 0 := (mul_eq_zero.mp hv).resolve_left (ne_of_gt hc)
    exact mul_nonpos_of_nonneg_of_nonpos hc.le (hsig u hu' v hv')
  have hsymm : ∀ i j, copyMatrix n H c i j = copyMatrix n H c j i := by
    intro i j
    simp only [copyMatrix, normalizedMatrix, Matrix.sub_apply, Matrix.add_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply, groupOuter]
    rw [hH]
    simp only [mul_comm (n i.1 : ℝ) (n j.1 : ℝ)]
    congr 1
    · congr 1
      apply Finset.sum_congr rfl
      intro u _
      ring
    · by_cases hij : i = j
      · subst j; rfl
      · simp [hij, Ne.symm hij]
  apply onePositive_of_dominated_compression (c • H.toBilin') _ (groupAverage n)
    (fun x y => (matrix_bilin_symm _ hsymm).eq x y) hcSig
  intro x
  rw [copyMatrix_form]
  change _ ≤ c * H.toBilin' (groupAverage n x) (groupAverage n x)
  apply sub_le_self
  apply Finset.sum_nonneg
  intro u _
  apply mul_nonneg _ (within_variance_nonnegative (n u) (fun i => x ⟨u, i⟩))
  exact div_nonneg (mul_nonneg hc.le (hdiag u)) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

omit [Fintype G] [DecidableEq G] in
lemma normalization_identity (n : ℕ) (a : ℝ) (hsmall : n < 2 → a = 0) :
    a / ((n : ℝ) * n) + (a / ((n : ℝ) * (n - 1 : ℕ))) / n =
      a / ((n : ℝ) * (n - 1 : ℕ)) := by
  by_cases hn : 2 ≤ n
  · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hn1 : (n : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    rw [hcast]
    field_simp
    ring
  · rw [hsmall (by omega)]
    simp

/-- The normalization has exactly the zero diagonal and the factorial
removal denominator, including single-copy and empty groups. -/
theorem copyMatrix_apply (n : G → ℕ) (H : Matrix G G ℝ) (c : ℝ)
    (hzero : ∀ u, n u < 2 → H u u = 0) (i j : Copies n) :
    copyMatrix n H c i j = if i = j then 0 else
      c * H i.1 j.1 / ((n i.1 : ℝ) *
        (if i.1 = j.1 then ((n i.1 - 1 : ℕ) : ℝ) else n j.1)) := by
  simp only [copyMatrix, normalizedMatrix, Matrix.sub_apply, Matrix.add_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, groupOuter, groupIndicator, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single i.1]
  · by_cases hg : i.1 = j.1
    · have hn := normalization_identity (n i.1) (c * H i.1 i.1)
        (fun h => by rw [hzero i.1 h, mul_zero])
      simp only [hg, ite_true, mul_one, withinCoefficient] at *
      rw [hn]
      by_cases hij : i = j <;> simp [hij]
    · have hij : i ≠ j := fun h => hg (congrArg Sigma.fst h)
      simp [hg, Ne.symm hg, hij]
  · intro u _ hu
    simp [Ne.symm hu]
  · simp

noncomputable def factorialProduct (n : G → ℕ) : ℝ := ∏ u, (n u).factorial

def removeOne (n : G → ℕ) (u : G) : G → ℕ := fun v => n v - if v = u then 1 else 0

def removeTwo (n : G → ℕ) (u v : G) : G → ℕ := removeOne (removeOne n u) v

omit [DecidableEq G] in
lemma factorialProduct_positive (n : G → ℕ) : 0 < factorialProduct n := by
  apply Finset.prod_pos
  intro u _
  exact_mod_cast Nat.factorial_pos (n u)

/-- Removing one labeled copy cancels precisely its coordinate count. -/
lemma factorialProduct_removeOne (n : G → ℕ) (u : G) (hu : 0 < n u) :
    factorialProduct (removeOne n u) = factorialProduct n / n u := by
  have hnu : (n u : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hu
  apply (eq_div_iff hnu).mpr
  unfold factorialProduct
  rw [← Finset.mul_prod_erase Finset.univ (fun v => ((removeOne n u v).factorial : ℝ))
    (Finset.mem_univ u),
    ← Finset.mul_prod_erase Finset.univ (fun v => ((n v).factorial : ℝ)) (Finset.mem_univ u)]
  have hrest : (∏ v ∈ Finset.univ.erase u, ((removeOne n u v).factorial : ℝ)) =
      ∏ v ∈ Finset.univ.erase u, ((n v).factorial : ℝ) := by
    apply Finset.prod_congr rfl
    intro v hv
    simp [removeOne, (Finset.mem_erase.mp hv).1]
  rw [hrest]
  have hfac : (n u : ℝ) * ((n u - 1).factorial : ℝ) = (n u).factorial := by
    exact_mod_cast Nat.mul_factorial_pred (Nat.ne_of_gt hu)
  simp only [removeOne, ite_true]
  calc
    _ = ((n u : ℝ) * ((n u - 1).factorial : ℝ)) *
        ∏ v ∈ Finset.univ.erase u, ((n v).factorial : ℝ) := by ring
    _ = _ := by rw [hfac]

/-- Two factorial reductions yield the exact cross-group or repeated-group
multiplicity denominator. -/
theorem factorialProduct_removeTwo (n : G → ℕ) (u v : G)
    (hu : 0 < n u) (hv : 0 < n v - if v = u then 1 else 0) :
    factorialProduct (removeTwo n u v) = factorialProduct n /
      ((n u : ℝ) * (if u = v then ((n u - 1 : ℕ) : ℝ) else n v)) := by
  rw [removeTwo, factorialProduct_removeOne _ v hv, factorialProduct_removeOne n u hu]
  by_cases huv : u = v
  · subst v
    simp only [removeOne, ite_true, div_div]
  · simp [removeOne, huv, Ne.symm huv, div_div]


omit [Fintype G] in
/-- Distinct labeled copies give valid one-per-coordinate or repeated-coordinate removals. -/
lemma distinct_copy_counts (n : G → ℕ) (i j : Copies n) (hij : i ≠ j) :
    0 < n i.1 ∧ 0 < n j.1 - if j.1 = i.1 then 1 else 0 := by
  rcases i with ⟨u, a⟩
  rcases j with ⟨v, b⟩
  have hu : 0 < n u := lt_of_le_of_lt (Nat.zero_le _) a.isLt
  have hv : 0 < n v := lt_of_le_of_lt (Nat.zero_le _) b.isLt
  refine ⟨hu, ?_⟩
  by_cases huv : u = v
  · subst v
    have hab : a ≠ b := fun h => hij (congrArg (Sigma.mk u) h)
    have hn : 2 ≤ n u := by
      by_contra hn
      have ha : a.val = 0 := by omega
      have hb : b.val = 0 := by omega
      exact hab (Fin.ext (ha.trans hb.symm))
    simp only [ite_true]
    omega
  · simp [Ne.symm huv, hv]

noncomputable def factorialMatrix (n : G → ℕ) (H : Matrix G G ℝ) (D : ℝ) :
    Matrix (Copies n) (Copies n) ℝ := fun i j => if i = j then 0 else
      H i.1 j.1 * factorialProduct (removeTwo n i.1 j.1) / D

/-- Exact factorial congruence with the normalized integer matrix. -/
theorem factorialMatrix_eq (n : G → ℕ) (H : Matrix G G ℝ) (D : ℝ)
    (hzero : ∀ u, n u < 2 → H u u = 0) :
    factorialMatrix n H D = copyMatrix n H (factorialProduct n / D) := by
  ext i j
  rw [copyMatrix_apply n H _ hzero]
  by_cases hij : i = j
  · simp [factorialMatrix, hij]
  obtain ⟨hi, hj⟩ := distinct_copy_counts n i j hij
  simp only [factorialMatrix, hij, ite_false]
  rw [factorialProduct_removeTwo n i.1 j.1 hi hj]
  ring

/-- The literal factorial weights have the binary signature implied by
their integer two-removal or remaining-capacity addition matrix. -/
theorem factorialMatrix_onePositive (n : G → ℕ) (H : Matrix G G ℝ) (D : ℝ)
    (hD : 0 < D) (hH : ∀ u v, H u v = H v u)
    (hsig : OnePositiveDirection H.toBilin') (hdiag : ∀ u, 0 ≤ H u u)
    (hzero : ∀ u, n u < 2 → H u u = 0) :
    OnePositiveDirection (factorialMatrix n H D).toBilin' := by
  rw [factorialMatrix_eq n H D hzero]
  exact copyMatrix_onePositive n H _ (div_pos (factorialProduct_positive n) hD) hH hsig hdiag

def ValidPair (n : G → ℕ) (u v : G) : Prop :=
  0 < n u ∧ 0 < n v - if v = u then 1 else 0

omit [Fintype G] in
lemma validPair_symm (n : G → ℕ) (u v : G) : ValidPair n u v ↔ ValidPair n v u := by
  by_cases huv : u = v
  · subst v
    rfl
  · simp [ValidPair, huv, Ne.symm huv, and_comm]

omit [Fintype G] in
lemma removeTwo_comm (n : G → ℕ) (u v : G) : removeTwo n u v = removeTwo n v u := by
  funext w
  dsimp [removeTwo, removeOne]
  omega

noncomputable def integerRemovalMatrix (h : (G → ℕ) → ℝ) (n : G → ℕ) : Matrix G G ℝ :=
  fun u v => if ValidPair n u v then h (removeTwo n u v) else 0

noncomputable def removalLiftMatrix (h : (G → ℕ) → ℝ) (n : G → ℕ) (D : ℝ) :
    Matrix (Copies n) (Copies n) ℝ := fun i j => if i = j then 0 else
      h (removeTwo n i.1 j.1) * factorialProduct (removeTwo n i.1 j.1) / D

/-- The actual omission matrix of the first factorial lift, with all
integer invalid-removal entries set to zero. -/
theorem removalLift_onePositive (h : (G → ℕ) → ℝ) (n : G → ℕ) (D : ℝ)
    (hD : 0 < D) (hh : ∀ r, 0 ≤ h r)
    (hsig : OnePositiveDirection (integerRemovalMatrix h n).toBilin') :
    OnePositiveDirection (removalLiftMatrix h n D).toBilin' := by
  have heq : removalLiftMatrix h n D = factorialMatrix n (integerRemovalMatrix h n) D := by
    ext i j
    by_cases hij : i = j
    · simp [removalLiftMatrix, factorialMatrix, hij]
    have hv := distinct_copy_counts n i j hij
    simp [removalLiftMatrix, factorialMatrix, hij, integerRemovalMatrix, ValidPair, hv]
  rw [heq]
  apply factorialMatrix_onePositive n _ D hD
  · intro u v
    simp only [integerRemovalMatrix, validPair_symm n u v, removeTwo_comm n u v]
  · exact hsig
  · intro u
    unfold integerRemovalMatrix
    split_ifs <;> simp [hh]
  · intro u hu
    have hn : ¬ValidPair n u u := by simp [ValidPair]; omega
    simp [integerRemovalMatrix, hn]

def addTwo (r : G → ℕ) (u v : G) : G → ℕ :=
  fun w => r w + (if w = u then 1 else 0) + (if w = v then 1 else 0)

noncomputable def integerAdditionMatrix (h : (G → ℕ) → ℝ) (r n : G → ℕ) : Matrix G G ℝ :=
  fun u v => if ValidPair n u v then h (addTwo r u v) else 0

noncomputable def additionLiftMatrix (h : (G → ℕ) → ℝ) (r n : G → ℕ) (D : ℝ) :
    Matrix (Copies n) (Copies n) ℝ := fun i j => if i = j then 0 else
      h (addTwo r i.1 j.1) * factorialProduct (removeTwo n i.1 j.1) / D

/-- The actual addition matrix of the complementary factorial lift uses
remaining-capacity factorials, and hence exactly the same congruence. -/
theorem additionLift_onePositive (h : (G → ℕ) → ℝ) (r n : G → ℕ) (D : ℝ)
    (hD : 0 < D) (hh : ∀ a, 0 ≤ h a)
    (hsig : OnePositiveDirection (integerAdditionMatrix h r n).toBilin') :
    OnePositiveDirection (additionLiftMatrix h r n D).toBilin' := by
  have heq : additionLiftMatrix h r n D = factorialMatrix n (integerAdditionMatrix h r n) D := by
    ext i j
    by_cases hij : i = j
    · simp [additionLiftMatrix, factorialMatrix, hij]
    have hv := distinct_copy_counts n i j hij
    simp [additionLiftMatrix, factorialMatrix, hij, integerAdditionMatrix, ValidPair, hv]
  rw [heq]
  apply factorialMatrix_onePositive n _ D hD
  · intro u v
    have heq : addTwo r u v = addTwo r v u := by funext w; dsimp [addTwo]; omega
    simp only [integerAdditionMatrix, validPair_symm n u v, heq]
  · exact hsig
  · intro u
    unfold integerAdditionMatrix
    split_ifs <;> simp [hh]
  · intro u hu
    have hn : ¬ValidPair n u u := by simp [ValidPair]; omega
    simp [integerAdditionMatrix, hn]


noncomputable def cellFactor (b x y : ℕ) : ℝ :=
  (x.factorial : ℝ) * y.factorial / b.factorial

noncomputable def complementCellFactor (b x y : ℕ) : ℝ :=
  ((b - x).factorial : ℝ) * (b - y).factorial / b.factorial

omit [Fintype G] [DecidableEq G] in
lemma cellFactor_positive (b x y : ℕ) : 0 < cellFactor b x y := by
  exact div_pos (mul_pos (by exact_mod_cast Nat.factorial_pos x)
    (by exact_mod_cast Nat.factorial_pos y)) (by exact_mod_cast Nat.factorial_pos b)

omit [Fintype G] [DecidableEq G] in
/-- On transversals, the two cell multipliers agree exactly. -/
lemma balanced_cell_factors (b x y : ℕ) (h : x + y = b) :
    complementCellFactor b x y = cellFactor b x y := by
  have hx : b - x = y := by omega
  have hy : b - y = x := by omega
  simp only [complementCellFactor, cellFactor, hx, hy]
  ring

omit [Fintype G] [DecidableEq G] in
/-- The empty-pair cell contributes `(x+1)(y+1)` to the lift ratio. -/
lemma empty_cell_factors (b x y : ℕ) (h : x + y + 1 = b) :
    complementCellFactor b x y = ((x : ℝ) + 1) * ((y : ℝ) + 1) * cellFactor b x y := by
  have hx : b - x = y + 1 := by omega
  have hy : b - y = x + 1 := by omega
  simp only [complementCellFactor, cellFactor, hx, hy, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  ring

omit [Fintype G] [DecidableEq G] in
/-- The full-pair cell contributes the reciprocal product `1/(xy)`. -/
lemma full_cell_factors (b x y : ℕ) (hx : x ≤ b) (hy : y ≤ b) (h : x + y = b + 1) :
    complementCellFactor b x y * ((x : ℝ) * y) = cellFactor b x y := by
  have hx0 : x ≠ 0 := by omega
  have hy0 : y ≠ 0 := by omega
  have hbx : b - x = y - 1 := by omega
  have hby : b - y = x - 1 := by omega
  have hxf : (x : ℝ) * ((x - 1).factorial : ℝ) = x.factorial := by
    exact_mod_cast Nat.mul_factorial_pred hx0
  have hyf : (y : ℝ) * ((y - 1).factorial : ℝ) = y.factorial := by
    exact_mod_cast Nat.mul_factorial_pred hy0
  simp only [complementCellFactor, cellFactor, hbx, hby]
  calc
    _ = ((x : ℝ) * ((x - 1).factorial : ℝ)) *
        ((y : ℝ) * ((y - 1).factorial : ℝ)) / b.factorial := by ring
    _ = _ := by rw [hxf, hyf]

omit [Fintype G] [DecidableEq G] in
lemma quotient_square_bounds (W A B : ℝ) (hW : 0 < W)
    (hA0 : 1 ≤ A) (hB0 : 1 ≤ B) (hA : A ≤ W ^ 2) (hB : B ≤ W ^ 2) :
    1 / W ^ 2 ≤ A / B ∧ A / B ≤ W ^ 2 := by
  have hWp : 0 < W ^ 2 := sq_pos_of_pos hW
  have hBp : 0 < B := by linarith
  constructor
  · apply (div_le_div_iff₀ hWp hBp).mpr
    nlinarith
  · apply (div_le_iff₀ hBp).mpr
    nlinarith

/-- The product ratio when one cell contains the hole, one contains the
full pair, and all remaining cells are balanced. -/
lemma defect_product_identity (F T : G → ℝ) (a b : G) (hab : a ≠ b) (A B : ℝ)
    (ha : T a = A * F a) (hb : T b = F b / B)
    (hrest : ∀ u, u ≠ a → u ≠ b → T u = F u) :
    (∏ u, T u) = (A / B) * ∏ u, F u := by
  have heq : T = fun u =>
      (if u = a then A else 1) * (if u = b then 1 / B else 1) * F u := by
    funext u
    by_cases hua : u = a
    · subst u
      simp [hab, ha]
    by_cases hub : u = b
    · subst u
      simp [Ne.symm hab, hb, div_eq_mul_inv, mul_comm]
    · simp [hua, hub, hrest u hua hub]
  rw [heq]
  simp only [Finset.prod_mul_distrib]
  simp [Finset.prod_ite_eq', div_eq_mul_inv, mul_assoc]

/-- The exact `q = W²` comparison between the two factorial lifts on a
single-hole/single-full defect, after their common positive base weight. -/
theorem defect_lift_comparison (b x y : G → ℕ) (a d : G) (had : a ≠ d)
    (W : ℕ) (hW : 0 < W) (hbW : ∀ u, b u < W)
    (hx : ∀ u, x u ≤ b u) (hy : ∀ u, y u ≤ b u)
    (ha : x a + y a + 1 = b a) (hd : x d + y d = b d + 1)
    (hrest : ∀ u, u ≠ a → u ≠ d → x u + y u = b u)
    (h : ℝ) (hh : 0 ≤ h) :
    (1 / (W : ℝ) ^ 2) * (h * ∏ u, cellFactor (b u) (x u) (y u)) ≤
      h * ∏ u, complementCellFactor (b u) (x u) (y u) ∧
    (h * ∏ u, complementCellFactor (b u) (x u) (y u)) ≤
      (W : ℝ) ^ 2 * (h * ∏ u, cellFactor (b u) (x u) (y u)) := by
  let A : ℝ := ((x a : ℝ) + 1) * ((y a : ℝ) + 1)
  let B : ℝ := (x d : ℝ) * y d
  have hxd : 1 ≤ x d := by have := hy d; omega
  have hyd : 1 ≤ y d := by have := hx d; omega
  have hBpos : 0 < B := by
    dsimp [B]
    exact mul_pos (by exact_mod_cast hxd) (by exact_mod_cast hyd)
  have hprod : (∏ u, complementCellFactor (b u) (x u) (y u)) =
      (A / B) * ∏ u, cellFactor (b u) (x u) (y u) := by
    apply defect_product_identity _ _ a d had A B
    · exact empty_cell_factors _ _ _ ha
    · exact (eq_div_iff (ne_of_gt hBpos)).mpr (full_cell_factors _ _ _ (hx d) (hy d) hd)
    · intro u hua hud
      exact balanced_cell_factors _ _ _ (hrest u hua hud)
  have hbounds : 1 / (W : ℝ) ^ 2 ≤ A / B ∧ A / B ≤ (W : ℝ) ^ 2 := by
    apply quotient_square_bounds _ A B (by exact_mod_cast hW)
    · dsimp [A]
      have hxa : (0 : ℝ) ≤ x a := Nat.cast_nonneg _
      have hya : (0 : ℝ) ≤ y a := Nat.cast_nonneg _
      nlinarith
    · dsimp [B]
      have hxd' : (1 : ℝ) ≤ x d := by exact_mod_cast hxd
      have hyd' : (1 : ℝ) ≤ y d := by exact_mod_cast hyd
      nlinarith
    · dsimp [A]
      have hxa : (x a : ℝ) + 1 ≤ W := by exact_mod_cast (by have := hx a; have := hbW a; omega : x a + 1 ≤ W)
      have hya : (y a : ℝ) + 1 ≤ W := by exact_mod_cast (by have := hy a; have := hbW a; omega : y a + 1 ≤ W)
      have hxa0 : 0 ≤ (x a : ℝ) + 1 := by positivity
      have hya0 : 0 ≤ (y a : ℝ) + 1 := by positivity
      nlinarith
    · dsimp [B]
      have hxdW : (x d : ℝ) ≤ W := by exact_mod_cast (by have := hx d; have := hbW d; omega : x d ≤ W)
      have hydW : (y d : ℝ) ≤ W := by exact_mod_cast (by have := hy d; have := hbW d; omega : y d ≤ W)
      have hxd0 : (0 : ℝ) ≤ x d := Nat.cast_nonneg _
      have hyd0 : (0 : ℝ) ≤ y d := Nat.cast_nonneg _
      nlinarith
  have hF : 0 ≤ h * ∏ u, cellFactor (b u) (x u) (y u) :=
    mul_nonneg hh (Finset.prod_nonneg (fun u _ => (cellFactor_positive _ _ _).le))
  rw [hprod]
  constructor
  · convert mul_le_mul_of_nonneg_right hbounds.1 hF using 1
    ring
  · convert mul_le_mul_of_nonneg_right hbounds.2 hF using 1
    ring


omit [DecidableEq G] in
/-- Agreement of the actual full factorial multipliers on every balanced profile. -/
theorem balanced_lift_agreement (b x y : G → ℕ)
    (hbalanced : ∀ u, x u + y u = b u) (h : ℝ) :
    h * (∏ u, complementCellFactor (b u) (x u) (y u)) =
      h * ∏ u, cellFactor (b u) (x u) (y u) := by
  congr 1
  apply Finset.prod_congr rfl
  intro u _
  exact balanced_cell_factors _ _ _ (hbalanced u)

end ContingencyTables.FactorialSignatures

end OAI
