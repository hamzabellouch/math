import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Concrete four-vector coordinates for a Bianchi gradient

The three quaternion actions are left multiplication by `i,j,k` on the real
four-dimensional Euclidean space. A symmetric matrix of four-vectors is
encoded by its three diagonal and three off-diagonal entries. Its divergence
constraint is the actual quaternionic Bianchi constraint of Section 2.
-/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators

abbrev Vec := EuclideanSpace ℝ (Fin 4)

/-- The fixed positive quaternion triple. -/
def quaternion (i : Fin 3) (q : Vec) : Vec :=
  ![WithLp.toLp 2 ![-q 1, q 0, -q 3, q 2],
    WithLp.toLp 2 ![-q 2, q 3, q 0, -q 1],
    WithLp.toLp 2 ![-q 3, -q 2, q 1, q 0]] i

def next (i : Fin 3) : Fin 3 := ![1, 2, 0] i

def previous (i : Fin 3) : Fin 3 := ![2, 0, 1] i

@[simp] theorem quaternion_add (i : Fin 3) (p q : Vec) :
    quaternion i (p + q) = quaternion i p + quaternion i q := by
  fin_cases i <;> ext j <;> fin_cases j <;> simp [quaternion] <;> ring

@[simp] theorem quaternion_smul (i : Fin 3) (a : ℝ) (q : Vec) :
    quaternion i (a • q) = a • quaternion i q := by
  fin_cases i <;> ext j <;> fin_cases j <;> simp [quaternion]

@[simp] theorem quaternion_neg (i : Fin 3) (q : Vec) :
    quaternion i (-q) = -quaternion i q := by
  simpa only [neg_one_smul] using quaternion_smul i (-1) q

@[simp] theorem quaternion_zero (i : Fin 3) : quaternion i 0 = 0 := by
  simpa using quaternion_smul i 0 (0 : Vec)

@[simp] theorem quaternion_square (i : Fin 3) (q : Vec) :
    quaternion i (quaternion i q) = -q := by
  fin_cases i <;> ext j <;> fin_cases j <;> simp [quaternion]

theorem quaternion_injective (i : Fin 3) : Function.Injective (quaternion i) := by
  intro p q h
  have hh := congrArg (quaternion i) h
  simpa using hh

/-- All three quaternion actions preserve the Euclidean metric. -/
@[simp] theorem quaternion_norm_sq (i : Fin 3) (q : Vec) :
    ‖quaternion i q‖ ^ 2 = ‖q‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq]
  fin_cases i <;> simp [quaternion, Fin.sum_univ_succ] <;> ring

@[simp] theorem quaternion_norm (i : Fin 3) (q : Vec) :
    ‖quaternion i q‖ = ‖q‖ := by
  nlinarith [quaternion_norm_sq i q, norm_nonneg (quaternion i q), norm_nonneg q]

/-- The normalized diagonal spectral shape. -/
structure Shape where
  s : Fin 3 → ℝ
  trace : ∑ i, s i = 0
  square : ∑ i, s i ^ 2 = 6

/-- This is `√3 * s̃`; using it avoids divisions by a square root in the
coordinate inverse. -/
def difference (s : Fin 3 → ℝ) (i : Fin 3) : ℝ := s (next i) - s (previous i)

theorem difference_sum (s : Fin 3 → ℝ) : ∑ i, difference s i = 0 := by
  simp [difference, next, previous, Fin.sum_univ_succ]
  ring

theorem Shape.difference_square (S : Shape) : ∑ i, difference S.s i ^ 2 = 18 := by
  have ht := S.trace
  have hn := S.square
  simp [Fin.sum_univ_succ] at ht hn
  simp [difference, next, previous, Fin.sum_univ_succ]
  nlinarith [sq_nonneg (S.s 0 + S.s 1 + S.s 2)]

theorem difference_orthogonal (s : Fin 3 → ℝ) : ∑ i, s i * difference s i = 0 := by
  simp [difference, next, previous, Fin.sum_univ_succ]
  ring

theorem Shape.difference_next_sub_previous (S : Shape) (i : Fin 3) :
    difference S.s (next i) - difference S.s (previous i) = -3 * S.s i := by
  have ht := S.trace
  simp [Fin.sum_univ_succ] at ht
  fin_cases i <;> simp [difference, next, previous] <;> linarith

/-- Completeness relation of the two orthogonal normalized spectral vectors. -/
theorem Shape.frame (S : Shape) (i j : Fin 3) :
    S.s i * S.s j / 6 + difference S.s i * difference S.s j / 18 =
      (if i = j then 1 else 0) - 1 / 3 := by
  have ht := S.trace
  have hn := S.square
  simp [Fin.sum_univ_succ] at ht hn
  have ht2 : S.s 2 = -S.s 0 - S.s 1 := by linarith
  have hn2 : S.s 0 ^ 2 + S.s 0 * S.s 1 + S.s 1 ^ 2 = 3 := by
    rw [ht2] at hn
    nlinarith
  fin_cases i <;> fin_cases j <;> simp [difference, next, previous, ht2] <;> nlinarith

/-- Symmetric three-by-three matrix with four-vector entries. `off i` is the
entry in positions `(next i, previous i)` and its transpose. -/
@[ext] structure Tensor where
  diagonal : Fin 3 → Vec
  off : Fin 3 → Vec

def Tensor.matrix (T : Tensor) : Fin 3 → Fin 3 → Vec :=
  ![![T.diagonal 0, T.off 2, T.off 1],
    ![T.off 2, T.diagonal 1, T.off 0],
    ![T.off 1, T.off 0, T.diagonal 2]]

theorem Tensor.matrix_symmetric (T : Tensor) (i j : Fin 3) :
    T.matrix i j = T.matrix j i := by
  fin_cases i <;> fin_cases j <;> rfl

def Tensor.traceFree (T : Tensor) : Prop := ∑ i, T.diagonal i = 0

/-- Quaternionic divergence in each matrix column. -/
def Tensor.divergence (T : Tensor) (i : Fin 3) : Vec :=
  quaternion i (T.diagonal i) + quaternion (next i) (T.off (previous i)) +
    quaternion (previous i) (T.off (next i))

/-- The concrete divergence is contraction of the quaternion action with
an actual matrix column. -/
theorem Tensor.divergence_eq_sum (T : Tensor) (i : Fin 3) :
    T.divergence i = ∑ j, quaternion j (T.matrix j i) := by
  fin_cases i <;> simp [Tensor.divergence, Tensor.matrix, next, previous,
    Fin.sum_univ_succ] <;> module

def Tensor.bianchi (T : Tensor) : Prop := ∀ i, T.divergence i = 0

def Tensor.auxiliary (T : Tensor) (i : Fin 3) : Vec := quaternion i (T.off i)

/-- Multiplying the divergence equation by the corresponding complex
structure gives the elementary cyclic constraint. -/
theorem Tensor.quaternion_divergence (T : Tensor) (i : Fin 3) :
    quaternion i (T.divergence i) =
      -(T.diagonal i + T.auxiliary (next i) - T.auxiliary (previous i)) := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [Tensor.divergence, Tensor.auxiliary, quaternion, next, previous] <;> ring

theorem Tensor.bianchi_iff (T : Tensor) : T.bianchi ↔
    ∀ i, T.diagonal i + T.auxiliary (next i) - T.auxiliary (previous i) = 0 := by
  constructor
  · intro h i
    have hh := congrArg (quaternion i) (h i)
    rw [T.quaternion_divergence, quaternion_zero] at hh
    exact neg_eq_zero.mp hh
  · intro h i
    apply quaternion_injective i
    rw [T.quaternion_divergence, h i, quaternion_zero, neg_zero]

/-- Explicit equation (2), in terms of `√3 * s̃`. -/
def parameters (S : Shape) (p k l : Vec) : Tensor where
  diagonal i := S.s i • p - difference S.s i • k
  off i := -quaternion i (l + S.s i • k + (difference S.s i / 3) • p)

@[simp] theorem parameters_auxiliary (S : Shape) (p k l : Vec) (i : Fin 3) :
    (parameters S p k l).auxiliary i = l + S.s i • k + (difference S.s i / 3) • p := by
  change quaternion i (-quaternion i _) = _
  rw [quaternion_neg, quaternion_square, neg_neg]

theorem parameters_traceFree (S : Shape) (p k l : Vec) :
    (parameters S p k l).traceFree := by
  unfold Tensor.traceFree parameters
  simp only [Finset.sum_sub_distrib, ← Finset.sum_smul]
  rw [S.trace, difference_sum]
  simp

theorem parameters_bianchi (S : Shape) (p k l : Vec) :
    (parameters S p k l).bianchi := by
  rw [Tensor.bianchi_iff]
  intro i
  change S.s i • p - difference S.s i • k +
    (parameters S p k l).auxiliary (next i) - (parameters S p k l).auxiliary (previous i) = 0
  rw [parameters_auxiliary, parameters_auxiliary]
  calc
    _ = (S.s i + (difference S.s (next i) - difference S.s (previous i)) / 3) • p +
        (-difference S.s i + S.s (next i) - S.s (previous i)) • k := by module
    _ = 0 := by
      rw [S.difference_next_sub_previous]
      have hp : S.s i + -3 * S.s i / 3 = 0 := by ring
      have hk : -difference S.s i + S.s (next i) - S.s (previous i) = 0 := by
        unfold difference
        ring
      rw [hp, hk]
      simp

/-- Radial coordinate recovered directly from the diagonal entries. -/
def radialCoordinate (S : Shape) (T : Tensor) : Vec :=
  (1 / 6 : ℝ) • ∑ i, S.s i • T.diagonal i

/-- Orthogonal diagonal coordinate recovered directly from the entries. -/
def secondCoordinate (S : Shape) (T : Tensor) : Vec :=
  (-1 / 18 : ℝ) • ∑ i, difference S.s i • T.diagonal i

theorem radialCoordinate_parameters (S : Shape) (p k l : Vec) :
    radialCoordinate S (parameters S p k l) = p := by
  unfold radialCoordinate parameters
  simp only [smul_sub, smul_smul, Finset.sum_sub_distrib, ← Finset.sum_smul]
  have hs : ∑ i, S.s i * S.s i = 6 := by simpa [pow_two] using S.square
  rw [hs, difference_orthogonal]
  module

theorem secondCoordinate_parameters (S : Shape) (p k l : Vec) :
    secondCoordinate S (parameters S p k l) = k := by
  unfold secondCoordinate parameters
  simp only [smul_sub, smul_smul, Finset.sum_sub_distrib, ← Finset.sum_smul]
  have hc : ∑ i, difference S.s i * S.s i = 0 := by
    simpa [mul_comm] using difference_orthogonal S.s
  have hd : ∑ i, difference S.s i * difference S.s i = 18 := by
    simpa [pow_two] using S.difference_square
  rw [hc, hd]
  module

/-- Every trace-free diagonal triple is recovered by the two coordinates. -/
theorem diagonal_reconstruction (S : Shape) (T : Tensor) (ht : T.traceFree) (i : Fin 3) :
    T.diagonal i = S.s i • radialCoordinate S T - difference S.s i • secondCoordinate S T := by
  unfold radialCoordinate secondCoordinate
  calc
    T.diagonal i = ∑ j : Fin 3, ((if i = j then (1 : ℝ) else 0) - 1 / 3) • T.diagonal j := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← Finset.smul_sum]
      have ht0 : ∑ j, T.diagonal j = 0 := ht
      simp [ht0]
    _ = ∑ j : Fin 3, (S.s i * S.s j / 6 + difference S.s i * difference S.s j / 18) •
        T.diagonal j := by simp only [S.frame]
    _ = _ := by
      ext j
      simp [Fin.sum_univ_succ]
      ring

/-- The final free coordinate is the common residual in the three off-diagonal
quaternion coordinates. -/
def thirdCoordinate (S : Shape) (T : Tensor) : Vec :=
  T.auxiliary 0 - S.s 0 • secondCoordinate S T -
    (difference S.s 0 / 3) • radialCoordinate S T

/-- More transparent defining expression for the third coordinate. -/
theorem thirdCoordinate_eq (S : Shape) (T : Tensor) :
    thirdCoordinate S T = T.auxiliary 0 - S.s 0 • secondCoordinate S T -
      (difference S.s 0 / 3) • radialCoordinate S T := by
  unfold thirdCoordinate
  module

theorem thirdCoordinate_parameters (S : Shape) (p k l : Vec) :
    thirdCoordinate S (parameters S p k l) = l := by
  rw [thirdCoordinate_eq, radialCoordinate_parameters, secondCoordinate_parameters,
    parameters_auxiliary]
  module

/-- A quaternionic Bianchi tensor is exactly the explicit parameter tensor;
this also gives uniqueness by the three coordinate recovery identities. -/
theorem parameters_reconstruction (S : Shape) (T : Tensor)
    (ht : T.traceFree) (hb : T.bianchi) :
    parameters S (radialCoordinate S T) (secondCoordinate S T) (thirdCoordinate S T) = T := by
  have hd := diagonal_reconstruction S T ht
  have hc := (T.bianchi_iff).mp hb
  let p := radialCoordinate S T
  let k := secondCoordinate S T
  let l := thirdCoordinate S T
  have hres (i : Fin 3) :
      T.auxiliary (next i) - S.s (next i) • k - (difference S.s (next i) / 3) • p =
      T.auxiliary (previous i) - S.s (previous i) • k - (difference S.s (previous i) / 3) • p := by
    apply sub_eq_zero.mp
    calc
      _ = T.auxiliary (next i) - T.auxiliary (previous i) -
          (S.s (next i) - S.s (previous i)) • k -
          ((difference S.s (next i) - difference S.s (previous i)) / 3) • p := by module
      _ = S.s i • p - difference S.s i • k +
          T.auxiliary (next i) - T.auxiliary (previous i) := by
        rw [S.difference_next_sub_previous]
        dsimp [difference]
        module
      _ = 0 := by
        change S.s i • radialCoordinate S T - difference S.s i • secondCoordinate S T +
          T.auxiliary (next i) - T.auxiliary (previous i) = 0
        rw [← hd i]
        exact hc i
  have hcommon (i : Fin 3) :
      T.auxiliary i - S.s i • k - (difference S.s i / 3) • p = l := by
    have h0 := hres 0
    have h1 := hres 1
    simp only [next, previous, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    have hl := thirdCoordinate_eq S T
    change l = T.auxiliary 0 - S.s 0 • k - (difference S.s 0 / 3) • p at hl
    fin_cases i
    · exact hl.symm
    · exact h0.trans (h1.trans hl.symm)
    · exact h1.trans hl.symm
  have hoff (i : Fin 3) : T.auxiliary i = l + S.s i • k + (difference S.s i / 3) • p := by
    calc
      _ = (T.auxiliary i - S.s i • k - (difference S.s i / 3) • p) +
          S.s i • k + (difference S.s i / 3) • p := by module
      _ = _ := by rw [hcommon]
  apply Tensor.ext
  · funext i
    exact (hd i).symm
  · funext i
    apply quaternion_injective i
    change (parameters S (radialCoordinate S T) (secondCoordinate S T)
      (thirdCoordinate S T)).auxiliary i = T.auxiliary i
    rw [parameters_auxiliary]
    exact (hoff i).symm

/-- Squared Hilbert--Schmidt norm of the symmetric vector-valued matrix. -/
def Tensor.squaredNorm (T : Tensor) : ℝ := ∑ i, ∑ j, ‖T.matrix i j‖ ^ 2

theorem Tensor.squaredNorm_eq (T : Tensor) :
    T.squaredNorm = (∑ i, ‖T.diagonal i‖ ^ 2) + 2 * ∑ i, ‖T.off i‖ ^ 2 := by
  simp [Tensor.squaredNorm, Tensor.matrix, Fin.sum_univ_succ]
  ring

private theorem sum_norm_two (a b : Fin 3 → ℝ) (p k : Vec) :
    (∑ i, ‖a i • p + b i • k‖ ^ 2) =
      (∑ i, a i ^ 2) * ‖p‖ ^ 2 + 2 * (∑ i, a i * b i) * inner ℝ p k +
        (∑ i, b i ^ 2) * ‖k‖ ^ 2 := by
  simp only [Fin.sum_univ_succ, norm_add_sq_real, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, real_inner_smul_left, real_inner_smul_right]
  ring

private theorem sum_norm_three (a b : Fin 3 → ℝ) (l k p : Vec) :
    (∑ i, ‖l + a i • k + b i • p‖ ^ 2) =
      3 * ‖l‖ ^ 2 + 2 * (∑ i, a i) * inner ℝ l k +
      2 * (∑ i, b i) * inner ℝ l p + (∑ i, a i ^ 2) * ‖k‖ ^ 2 +
      2 * (∑ i, a i * b i) * inner ℝ k p + (∑ i, b i ^ 2) * ‖p‖ ^ 2 := by
  simp only [Fin.sum_univ_succ, norm_add_sq_real, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, inner_add_left, real_inner_smul_left, real_inner_smul_right]
  ring

theorem parameters_diagonal_energy (S : Shape) (p k l : Vec) :
    (∑ i, ‖(parameters S p k l).diagonal i‖ ^ 2) = 6 * ‖p‖ ^ 2 + 18 * ‖k‖ ^ 2 := by
  have h := sum_norm_two S.s (fun i => -difference S.s i) p k
  simp only [neg_smul, ← sub_eq_add_neg, mul_neg, neg_sq,
    Finset.sum_neg_distrib, S.square, difference_orthogonal, S.difference_square] at h
  simpa [parameters] using h

theorem parameters_off_energy (S : Shape) (p k l : Vec) :
    (∑ i, ‖(parameters S p k l).off i‖ ^ 2) =
      3 * ‖l‖ ^ 2 + 6 * ‖k‖ ^ 2 + 2 * ‖p‖ ^ 2 := by
  have hb : ∑ i, difference S.s i / 3 = 0 := by
    rw [← Finset.sum_div, difference_sum]
    norm_num
  have hb2 : ∑ i, (difference S.s i / 3) ^ 2 = 2 := by
    simp only [div_pow]
    rw [← Finset.sum_div, S.difference_square]
    norm_num
  have hab : ∑ i, S.s i * (difference S.s i / 3) = 0 := by
    simp only [← mul_div_assoc]
    rw [← Finset.sum_div, difference_orthogonal]
    norm_num
  have h := sum_norm_three S.s (fun i => difference S.s i / 3) l k p
  simp only [S.trace, hb, S.square, hab, hb2, mul_zero, zero_mul, add_zero] at h
  change (∑ i, ‖-quaternion i (l + S.s i • k + (difference S.s i / 3) • p)‖ ^ 2) = _
  simp only [norm_neg, quaternion_norm]
  exact h

/-- The exact energy identity in (2), including the multiplicity of the
symmetric off-diagonal entries. -/
theorem parameters_energy (S : Shape) (p k l : Vec) :
    (parameters S p k l).squaredNorm / 6 =
      (5 / 3) * ‖p‖ ^ 2 + 5 * ‖k‖ ^ 2 + ‖l‖ ^ 2 := by
  rw [Tensor.squaredNorm_eq, parameters_diagonal_energy, parameters_off_energy]
  ring

/-- The refined Kato inequality follows from the full parametrization for
every symmetric tensor satisfying the actual Bianchi constraint. -/
theorem refined_kato (S : Shape) (T : Tensor) (ht : T.traceFree) (hb : T.bianchi) :
    (5 / 3) * ‖radialCoordinate S T‖ ^ 2 ≤ T.squaredNorm / 6 := by
  have h := parameters_energy S (radialCoordinate S T) (secondCoordinate S T) (thirdCoordinate S T)
  rw [parameters_reconstruction S T ht hb] at h
  nlinarith [sq_nonneg ‖secondCoordinate S T‖, sq_nonneg ‖thirdCoordinate S T‖]

end
end PositiveEinsteinFour.Bianchi

end OAI
