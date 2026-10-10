import OAI.Analysis.GroupDeterminants.Model

namespace OAI

universe uR ud ul um ur

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

def CompanionInput : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
    (H : Type) (_ : Group H) (_ : Group.FG H)
    (a b : MonoidAlgebra K H), a * b = 1 ∧ b * a ≠ 1

theorem no_finite_group_input (K H : Type) [Field K] [Finite K] [Group H] [Finite H]
    (a b : MonoidAlgebra K H) (h : a * b = 1) : b * a = 1 := by
  have : Finite (H →₀ K) :=
    Finite.of_injective (fun f : H →₀ K => (f : H → K)) DFunLike.coe_injective
  have : Finite (MonoidAlgebra K H) :=
    Finite.of_equiv (H →₀ K) MonoidAlgebra.coeffEquiv.symm
  exact mul_eq_one_symm h

theorem regularOperator_unique {G : Type} [Group G] {n : ℕ}
    {A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℤ G)}
    {T S : Hilbert G n →L[ℂ] Hilbert G n}
    (hT : IsRegularOperator A T) (hS : IsRegularOperator A S) : T = S := by
  ext ξ ⟨i, h⟩
  exact (hT ξ i h).trans (hS ξ i h).symm

theorem fkDet_pos {G : Type} [Group G] {n : ℕ}
    (T : Hilbert G n →L[ℂ] Hilbert G n) : 0 < fkDet T :=
  Real.exp_pos _

section Defect
variable {R : Type uR} [Ring R]

theorem defect_idempotent {x y : R} (h : x * y = 1) :
    (1 - y * x) * (1 - y * x) = 1 - y * x := by
  have hy : y * x * (y * x) = y * x := by
    calc
      y * x * (y * x) = y * (x * y) * x := by simp only [mul_assoc]
      _ = y * x := by rw [h, mul_one]
  calc
    (1 - y * x) * (1 - y * x) = 1 - y * x - y * x + y * x * (y * x) := by
      noncomm_ring
    _ = 1 - y * x := by rw [hy]; noncomm_ring

theorem mul_defect {x y : R} (h : x * y = 1) : x * (1 - y * x) = 0 := by
  simp only [mul_sub, mul_one, ← mul_assoc, h, one_mul, sub_self]

theorem defect_mul {x y : R} (h : x * y = 1) : (1 - y * x) * y = 0 := by
  simp only [sub_mul, one_mul, mul_assoc, h, mul_one, sub_self]

theorem defect_ne_zero {x y : R} (h : y * x ≠ 1) : 1 - y * x ≠ 0 := by
  exact sub_ne_zero.mpr h.symm

end Defect

section MatrixDefect
variable {R : Type uR} {d : Type ud} {l : Type ul} [Ring R] [Fintype d] [DecidableEq d]

theorem defect_factorization (X Y : Matrix d d R) (hXY : X * Y = 1)
    (f : Matrix l d R) (w : Matrix d l R) :
    Matrix.fromRows X (f * (1 - Y * X)) * Matrix.fromCols Y ((1 - Y * X) * w) =
      Matrix.fromBlocks 1 0 0 (f * (1 - Y * X) * w) := by
  rw [Matrix.fromRows_mul_fromCols, hXY]
  congr 1
  · rw [← Matrix.mul_assoc, mul_defect hXY, Matrix.zero_mul]
  · rw [Matrix.mul_assoc, defect_mul hXY, Matrix.mul_zero]
  · rw [← Matrix.mul_assoc, Matrix.mul_assoc f, defect_idempotent hXY]

end MatrixDefect

section CornerLifting
variable {R : Type uR} [Ring R]

def cornerSeries (e z : R) (k : ℕ) : R :=
  e * ∑ i ∈ Finset.range k, (e - z) ^ i

theorem cornerSeries_spec (e z : R) (he : e * e = e)
    (hez : e * z = z) (hze : z * e = z) (k : ℕ) (hk : (e - z) ^ k = 0) :
    cornerSeries e z k * z = e ∧ z * cornerSeries e z k = e ∧
      e * cornerSeries e z k = cornerSeries e z k ∧
      cornerSeries e z k * e = cornerSeries e z k := by
  let w := e - z
  let s := ∑ i ∈ Finset.range k, w ^ i
  have hew : e * w = w := by simp only [w, mul_sub, he, hez]
  have hwe : w * e = w := by simp only [w, sub_mul, he, hze]
  have hew' : Commute e w := hew.trans hwe.symm
  have hes : Commute e s :=
    Commute.sum_right _ _ _ (fun i _ => hew'.pow_right i)
  have hz : z = e * (1 - w) := by simp only [mul_sub, mul_one, hew, w]; noncomm_ring
  have hinv : s * (1 - w) = 1 := by
    simpa only [w, hk, sub_zero] using geom_sum_mul_neg w k
  have hinv' : (1 - w) * s = 1 := by
    simpa only [w, hk, sub_zero] using mul_neg_geom_sum w k
  change (e * s) * z = e ∧ z * (e * s) = e ∧
    e * (e * s) = e * s ∧ (e * s) * e = e * s
  have hq : (e * s) * e = e * s := by
    rw [mul_assoc, ← hes.eq, ← mul_assoc, he]
  refine ⟨?_, ?_, ?_, hq⟩
  · rw [hz, ← mul_assoc, hq, mul_assoc, hinv, mul_one]
  · calc
      z * (e * s) = z * s := by rw [← mul_assoc, hze]
      _ = e := by rw [hz, mul_assoc, hinv', mul_one]
  · rw [← mul_assoc, he]

theorem lift_rectangular_factorization {m : Type um} {r : Type ur} [Fintype m] [DecidableEq m]
    [Fintype r] (e : Matrix m m R) (he : e * e = e)
    (u₀ : Matrix m r R) (v₀ : Matrix r m R) (k : ℕ)
    (hk : (e - e * u₀ * v₀ * e) ^ k = 0) :
    ∃ u : Matrix m r R, ∃ v : Matrix r m R, u * v = e := by
  let z := e * u₀ * v₀ * e
  have hez : e * z = z := by
    dsimp [z]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, he]
  have hze : z * e = z := by
    dsimp [z]
    rw [Matrix.mul_assoc (e * u₀ * v₀), he]
  obtain ⟨hqz, _, _, _⟩ := cornerSeries_spec e z he hez hze k hk
  refine ⟨cornerSeries e z k * e * u₀, v₀ * e, ?_⟩
  simpa only [z, Matrix.mul_assoc] using hqz

end CornerLifting

end GroupRingDeterminant

end

end OAI
