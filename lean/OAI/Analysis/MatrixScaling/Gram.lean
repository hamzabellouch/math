import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Basic.Complex.BigOperators
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

/-! Gram determinant expansions and exponential convexity. -/

noncomputable section
open scoped BigOperators
namespace Kaplansky
variable {ι : Type*} [Fintype ι]

/-- Strict positivity of the unnormalized weighted variance. -/
theorem weighted_variance_pos (w a : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (i j : ι) (hi : 0 < w i) (hj : 0 < w j) (hij : a i ≠ a j) :
    0 < (∑ k, w k) * (∑ k, w k * (a k)^2) - (∑ k, w k * a k)^2 := by
  let S := ∑ k, w k
  let M := ∑ k, w k * a k
  let m := M/S
  have hS : 0 < S := lt_of_lt_of_le hi
    (Finset.single_le_sum (fun k _ => hw k) (Finset.mem_univ i))
  have he : ∑ k, w k * (a k-m)^2 =
      (∑ k, w k*(a k)^2) - 2*m*M + m^2*S := by
    calc
      ∑ k, w k * (a k-m)^2 =
          ∑ k, (w k*(a k)^2 - 2*m*(w k*a k) + m^2*w k) := by
        apply Finset.sum_congr rfl; intro k _; ring
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
  have hn : ∀ k, 0 ≤ w k * (a k-m)^2 := fun k => mul_nonneg (hw k) (sq_nonneg _)
  have hpos : 0 < ∑ k, w k * (a k-m)^2 := by
    by_cases him : a i = m
    · have hjm : a j ≠ m := fun h => hij (him.trans h.symm)
      exact lt_of_lt_of_le (mul_pos hj (sq_pos_of_ne_zero (sub_ne_zero.mpr hjm)))
        (Finset.single_le_sum (fun k _ => hn k) (Finset.mem_univ j))
    · exact lt_of_lt_of_le (mul_pos hi (sq_pos_of_ne_zero (sub_ne_zero.mpr him)))
        (Finset.single_le_sum (fun k _ => hn k) (Finset.mem_univ i))
  have hid : S * (∑ k, w k*(a k)^2) - M^2 = S * (∑ k, w k*(a k-m)^2) := by
    rw [he]
    dsimp [m]
    field_simp
    ring
  change 0 < S * (∑ k, w k*(a k)^2) - M^2
  rw [hid]
  exact mul_pos hS hpos

def expMoment (c a : ι → ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  ∑ i, c i * (a i)^k * Real.exp (a i*u)

theorem hasDerivAt_expMoment (c a : ι → ℝ) (k : ℕ) (u : ℝ) :
    HasDerivAt (expMoment c a k) (expMoment c a (k+1) u) u := by
  have h := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    (((hasDerivAt_id u).const_mul (a i)).exp).const_mul (c i * (a i)^k))
  have hf : expMoment c a k = ∑ i, fun y => c i*(a i)^k*Real.exp (a i*id y) := by
    funext y
    simp [expMoment]
  have hv : expMoment c a (k+1) u =
      ∑ i, c i*(a i)^k*(Real.exp (a i*id u)*(a i*1)) := by
    simp [expMoment, pow_succ, mul_assoc, mul_comm, mul_left_comm]
  rw [hf, hv]
  exact h

theorem expMoment_zero_pos (c a : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (i : ι) (hi : 0 < c i) (u : ℝ) : 0 < expMoment c a 0 u := by
  simp only [expMoment, pow_zero, mul_one]
  exact lt_of_lt_of_le (mul_pos hi (Real.exp_pos _))
    (Finset.single_le_sum (fun j _ => mul_nonneg (hc j) (Real.exp_pos _).le) (Finset.mem_univ i))

theorem strictConvexOn_log_expSum (c a : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (i j : ι) (hi : 0 < c i) (hj : 0 < c j) (hij : a i ≠ a j) :
    StrictConvexOn ℝ Set.univ (fun u => Real.log (∑ k, c k * Real.exp (a k*u))) := by
  have hz (u : ℝ) := expMoment_zero_pos c a hc i hi u
  have hd (u : ℝ) : HasDerivAt (fun u => Real.log (expMoment c a 0 u))
      (expMoment c a 1 u / expMoment c a 0 u) u :=
    (hasDerivAt_expMoment c a 0 u).log (ne_of_gt (hz u))
  have hd' : deriv (fun u => Real.log (expMoment c a 0 u)) =
      fun u => expMoment c a 1 u / expMoment c a 0 u := funext (fun u => (hd u).deriv)
  have hc' : StrictConvexOn ℝ Set.univ (fun u => Real.log (expMoment c a 0 u)) := by
    apply strictConvexOn_of_deriv2_pos convex_univ
    · exact (continuous_iff_continuousAt.mpr (fun u => (hd u).continuousAt)).continuousOn
    · intro u _
      change 0 < deriv (deriv (fun u => Real.log (expMoment c a 0 u))) u
      rw [hd']
      change 0 < deriv (expMoment c a 1 / expMoment c a 0) u
      rw [((hasDerivAt_expMoment c a 1 u).div
        (hasDerivAt_expMoment c a 0 u) (ne_of_gt (hz u))).deriv]
      apply div_pos _ (sq_pos_of_pos (hz u))
      have hv := weighted_variance_pos (fun k => c k*Real.exp (a k*u)) a
        (fun k => mul_nonneg (hc k) (Real.exp_pos _).le) i j
        (mul_pos hi (Real.exp_pos _)) (mul_pos hj (Real.exp_pos _)) hij
      simpa only [expMoment, Nat.reduceAdd, pow_zero, pow_one, mul_one, mul_comm, mul_left_comm,
        mul_assoc, pow_two] using hv
  simpa only [expMoment, pow_zero, mul_one] using hc'

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder
namespace Kaplansky
variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Multivariate principal-minor expansion, with one scalar for each row. -/
theorem det_one_add_diagonal_mul {R : Type*} [CommRing R]
    (G : Matrix n n R) (t : n → R) :
    (1 + Matrix.diagonal t * G).det =
      ∑ s : Finset n, (∏ i ∈ s, t i) *
        (G.submatrix (Subtype.val : s → n) Subtype.val).det := by
  let D := (Matrix.detRowAlternating : (n → R) [⋀^n]→ₗ[R] R)
  rw [add_comm]
  have hg : Matrix.diagonal t * G = Matrix.of (fun i => t i • G i) := by
    ext i j
    simp [Matrix.diagonal_mul]
  rw [hg]
  change D ((fun i => t i • G i) + (fun i => (1 : Matrix n n R) i)) = _
  rw [D.map_add_univ]
  apply Finset.sum_congr rfl
  intro s _
  have hsmul : s.piecewise (fun i => t i • G i) (1 : Matrix n n R) =
      fun i => (if i ∈ s then t i else 1) • s.piecewise G (1 : Matrix n n R) i := by
    funext i j
    simp only [Finset.piecewise, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hsmul, D.map_smul_univ]
  rw [smul_eq_mul]
  change (∏ i, if i ∈ s then t i else 1) *
    (Matrix.of (s.piecewise G (1 : Matrix n n R))).det = _
  have hd := Matrix.det_piecewise_one_eq_submatrix_det G s
  change (Matrix.of (s.piecewise G (1 : Matrix n n R))).det = _ at hd
  rw [hd]
  simp only [Finset.prod_ite_mem, Finset.univ_inter]

theorem gram_determinant_expansion (W : Matrix m n ℂ) (t : n → ℂ) :
    (1 + W * Matrix.diagonal t * W.conjTranspose).det =
      ∑ s : Finset n, (∏ i ∈ s, t i) *
        ((W.conjTranspose * W).submatrix (Subtype.val : s → n) Subtype.val).det := by
  rw [Matrix.mul_assoc, Matrix.det_one_add_mul_comm, Matrix.mul_assoc]
  exact det_one_add_diagonal_mul _ _

omit [DecidableEq m] in
theorem gram_minor_nonneg (W : Matrix m n ℂ) (s : Finset n) :
    0 ≤ ((W.conjTranspose * W).submatrix (Subtype.val : s → n) Subtype.val).det := by
  exact (Matrix.posSemidef_conjTranspose_mul_self W).submatrix _ |>.det_nonneg

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder
namespace Kaplansky
variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

def gramCoefficient (W : Matrix m n ℂ) (s : Finset n) : ℝ :=
  ((W.conjTranspose * W).submatrix (Subtype.val : s → n) Subtype.val).det.re

omit [DecidableEq m] in
theorem gramCoefficient_nonneg (W : Matrix m n ℂ) (s : Finset n) :
    0 ≤ gramCoefficient W s := (gram_minor_nonneg W s).1

omit [Fintype n] [DecidableEq m] in
@[simp] theorem gramCoefficient_empty (W : Matrix m n ℂ) :
    gramCoefficient W ∅ = 1 := by simp [gramCoefficient]

omit [Fintype n] [DecidableEq m] in
theorem gramCoefficient_singleton (W : Matrix m n ℂ) (j : n) :
    gramCoefficient W {j} = ∑ i, Complex.normSq (W i j) := by
  unfold gramCoefficient
  rw [Matrix.det_eq_elem_of_subsingleton _ ⟨j,Finset.mem_singleton_self j⟩]
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have he := map_sum Complex.reAddGroupHom (fun i => star (W i j) * W i j) Finset.univ
  change (∑ i, star (W i j) * W i j).re = ∑ i, (star (W i j) * W i j).re at he
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

omit [Fintype n] [DecidableEq m] in
theorem gramCoefficient_singleton_pos (W : Matrix m n ℂ) (i : m) (j : n)
    (h : W i j ≠ 0) : 0 < gramCoefficient W {j} := by
  rw [gramCoefficient_singleton]
  exact lt_of_lt_of_le (Complex.normSq_pos.mpr h)
    (Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (W k j)) (Finset.mem_univ i))

theorem gram_determinant_expSum (W : Matrix m n ℂ) (a : n → ℝ) (u : ℝ) :
    (1 + W * Matrix.diagonal (fun i => (Real.exp (a i*u) : ℂ)) * W.conjTranspose).det.re =
      ∑ s : Finset n, gramCoefficient W s * Real.exp ((∑ i ∈ s, a i)*u) := by
  rw [gram_determinant_expansion]
  have he := map_sum Complex.reAddGroupHom
    (fun s : Finset n => (∏ i ∈ s, (Real.exp (a i*u) : ℂ)) *
      ((W.conjTranspose * W).submatrix (Subtype.val : s → n) Subtype.val).det) Finset.univ
  change Complex.re (∑ s : Finset n, _) = ∑ s : Finset n, Complex.re _ at he
  rw [he]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Complex.ofReal_prod, ← Real.exp_sum, ← Finset.sum_mul]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    gramCoefficient, mul_comm]

theorem strictConvexOn_log_gram (W : Matrix m n ℂ) (a : n → ℝ)
    (i : m) (j : n) (hW : W i j ≠ 0) (ha : a j ≠ 0) :
    StrictConvexOn ℝ Set.univ (fun u => Real.log
      (1 + W * Matrix.diagonal (fun k => (Real.exp (a k*u) : ℂ)) * W.conjTranspose).det.re) := by
  have hc := strictConvexOn_log_expSum (gramCoefficient W)
    (fun s : Finset n => ∑ k ∈ s, a k) (gramCoefficient_nonneg W)
    ∅ {j} (by simp) (gramCoefficient_singleton_pos W i j hW) (by simpa using ha.symm)
  simpa only [← gram_determinant_expSum] using hc

end Kaplansky

end

end OAI
