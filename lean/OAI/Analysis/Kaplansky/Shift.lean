import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace OAI

/-! Hilbert shifts, their relations, and block operator bounds. -/

noncomputable section
open scoped BigOperators ENNReal
namespace Kaplansky
variable {E : ℕ → Type*} [∀ j, NormedAddCommGroup (E j)]
  [∀ j, InnerProductSpace ℂ (E j)]

abbrev FiberHilbertSum (E : ℕ → Type*) [∀ j, NormedAddCommGroup (E j)] := lp E 2

def levelInclusion (j : ℕ) : E j →ₗᵢ[ℂ] FiberHilbertSum E where
  toLinearMap := lp.lsingle 2 j
  norm_map' v := lp.norm_single (by norm_num) j v

theorem successor_orthogonal : OrthogonalFamily ℂ (fun j => E (j+1))
    (fun j => levelInclusion (j+1)) := by
  intro i j hij v w
  change inner ℂ (lp.single 2 (i+1) v) (lp.single 2 (j+1) w) = 0
  rw [lp.inner_single_left]
  simp [Pi.single_eq_of_ne (show i+1 ≠ j+1 by omega)]

variable [∀ j, CompleteSpace (E j)]

/-- Isometric insertion of a zero level at the start of the sum. -/
def successorInclusion : lp (fun j => E (j+1)) 2 →ₗᵢ[ℂ] FiberHilbertSum E :=
  successor_orthogonal.linearIsometry

def forwardShift (T : ∀ j, E j →L[ℂ] E (j+1)) (hT : ∀ j, ‖T j‖ ≤ 1) :
    FiberHilbertSum E →L[ℂ] FiberHilbertSum E :=
  successorInclusion.toContinuousLinearMap.comp (lp.mapCLM 2 T zero_le_one hT)

theorem forwardShift_norm_le (T : ∀ j, E j →L[ℂ] E (j+1)) (hT : ∀ j, ‖T j‖ ≤ 1) :
    ‖forwardShift T hT‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖successorInclusion (lp.mapCLM 2 T zero_le_one hT f)‖ ≤ 1 * ‖f‖
  rw [successorInclusion.norm_map]
  exact (lp.mapCLM 2 T zero_le_one hT).le_of_opNorm_le (lp.norm_mapCLM_le ..) f

theorem forwardShift_single (T : ∀ j, E j →L[ℂ] E (j+1)) (hT : ∀ j, ‖T j‖ ≤ 1)
    (j : ℕ) (v : E j) : forwardShift T hT (lp.single 2 j v) =
      lp.single 2 (j+1) (T j v) := by
  have he : lp.mapCLM 2 T zero_le_one hT (lp.single 2 j v) =
      lp.single 2 j (T j v) := by
    ext k
    by_cases hk : k = j
    · subst k; simp
    · simp [Pi.single_eq_of_ne hk]
  change successorInclusion (lp.mapCLM 2 T zero_le_one hT (lp.single 2 j v)) = _
  rw [he]
  exact OrthogonalFamily.linearIsometry_apply_single _ _

end Kaplansky

end

noncomputable section
open scoped BigOperators ENNReal
namespace Kaplansky
variable {E : ℕ → Type*} [∀ j, NormedAddCommGroup (E j)]
  [∀ j, InnerProductSpace ℂ (E j)] [∀ j, CompleteSpace (E j)]

/-- A forward shift has zero output in degree zero. -/
theorem forwardShift_apply_zero (T : ∀ j, E j →L[ℂ] E (j+1)) (hT : ∀ j, ‖T j‖ ≤ 1)
    (f : FiberHilbertSum E) : forwardShift T hT f 0 = 0 := by
  have he : (lp.evalCLM ℂ E 2 0).comp (forwardShift T hT) = 0 := by
    apply lp.ext_continuousLinearMap (by norm_num)
    intro j
    ext v
    change forwardShift T hT (lp.single 2 j v) 0 = 0
    rw [forwardShift_single]
    simp
  exact DFunLike.congr_fun he f

/-- On degree j+1, the forward shift is exactly its j-th block. -/
theorem forwardShift_apply_succ (T : ∀ j, E j →L[ℂ] E (j+1)) (hT : ∀ j, ‖T j‖ ≤ 1)
    (f : FiberHilbertSum E) (j : ℕ) : forwardShift T hT f (j+1) = T j (f j) := by
  have he : (lp.evalCLM ℂ E 2 (j+1)).comp (forwardShift T hT) =
      (T j).comp (lp.evalCLM ℂ E 2 j) := by
    apply lp.ext_continuousLinearMap (by norm_num)
    intro k
    ext v
    change forwardShift T hT (lp.single 2 k v) (j+1) = T j (lp.single 2 k v j)
    rw [forwardShift_single]
    by_cases hk : j = k
    · subst k; simp
    · simp [Pi.single_eq_of_ne hk, Pi.single_eq_of_ne (show j+1 ≠ k+1 by omega)]
  exact DFunLike.congr_fun he f

/-- The adjoint lowers degree, using the adjoint of the actual block. -/
theorem forwardShift_adjoint_apply (T : ∀ j, E j →L[ℂ] E (j+1)) (hT : ∀ j, ‖T j‖ ≤ 1)
    (f : FiberHilbertSum E) (j : ℕ) :
    (forwardShift T hT).adjoint f j = (T j).adjoint (f (j+1)) := by
  apply ext_inner_left ℂ
  intro v
  rw [← lp.inner_single_left j v, ContinuousLinearMap.adjoint_inner_right,
    forwardShift_single, lp.inner_single_left, ContinuousLinearMap.adjoint_inner_right]

theorem forwardShift_adjoint_single_zero (T : ∀ j, E j →L[ℂ] E (j+1))
    (hT : ∀ j, ‖T j‖ ≤ 1) (v : E 0) :
    (forwardShift T hT).adjoint (lp.single 2 0 v) = 0 := by
  ext j
  rw [forwardShift_adjoint_apply]
  simp

theorem forwardShift_adjoint_single_succ (T : ∀ j, E j →L[ℂ] E (j+1))
    (hT : ∀ j, ‖T j‖ ≤ 1) (j : ℕ) (v : E (j+1)) :
    (forwardShift T hT).adjoint (lp.single 2 (j+1) v) =
      lp.single 2 j ((T j).adjoint v) := by
  ext k
  rw [forwardShift_adjoint_apply]
  by_cases hk : k = j
  · subst k; simp
  · simp [Pi.single_eq_of_ne hk, Pi.single_eq_of_ne (show k+1 ≠ j+1 by omega)]

end Kaplansky

end

noncomputable section
open scoped BigOperators ENNReal ComplexOrder
namespace Kaplansky
variable {E : ℕ → Type*} [∀ j, NormedAddCommGroup (E j)]
  [∀ j, InnerProductSpace ℂ (E j)] [∀ j, CompleteSpace (E j)]
variable {n : ℕ} (T : Fin n → ∀ j, E j →L[ℂ] E (j+1))
  (hT : ∀ i j, ‖T i j‖ ≤ 1)

theorem forwardShift_column
    (hcol : ∀ j, ∑ i, (T i j).adjoint.comp (T i j) = ContinuousLinearMap.id ℂ (E j)) :
    ∑ i, (forwardShift (T i) (hT i)).adjoint * forwardShift (T i) (hT i) = 1 := by
  ext f j
  simp only [sum_apply, lp.coeFn_sum, Finset.sum_apply,
    mul_apply_eq_comp, forwardShift_adjoint_apply, forwardShift_apply_succ]
  simpa using DFunLike.congr_fun (hcol j) (f j)

theorem forwardShift_row_zero (f : FiberHilbertSum E) :
    (∑ i, forwardShift (T i) (hT i) * (forwardShift (T i) (hT i)).adjoint) f 0 = 0 := by
  simp only [sum_apply, lp.coeFn_sum, Finset.sum_apply,
    mul_apply_eq_comp, forwardShift_apply_zero, Finset.sum_const_zero]

theorem forwardShift_row_succ (f : FiberHilbertSum E) (j : ℕ) :
    (∑ i, forwardShift (T i) (hT i) * (forwardShift (T i) (hT i)).adjoint) f (j+1) =
      (∑ i, (T i j).comp (T i j).adjoint) (f (j+1)) := by
  simp only [sum_apply, lp.coeFn_sum, Finset.sum_apply,
    mul_apply_eq_comp, forwardShift_apply_succ, forwardShift_adjoint_apply,
    ContinuousLinearMap.comp_apply]

theorem forwardShift_row_positive (c : ℝ) (hc : 0 ≤ c)
    (hrow : ∀ j, ((c : ℂ) • ContinuousLinearMap.id ℂ (E (j+1)) -
      ∑ i, (T i j).comp (T i j).adjoint).IsPositive) :
    ((c : ℂ) • (1 : FiberHilbertSum E →L[ℂ] FiberHilbertSum E) -
      ∑ i, forwardShift (T i) (hT i) * (forwardShift (T i) (hT i)).adjoint).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
  intro f
  suffices hn : 0 ≤ inner ℂ (((c : ℂ) • (1 : FiberHilbertSum E →L[ℂ] FiberHilbertSum E) -
      ∑ i, forwardShift (T i) (hT i) * (forwardShift (T i) (hT i)).adjoint) f) f by
    rcases RCLike.nonneg_iff.mp hn with ⟨hre,him⟩
    exact ⟨Complex.ext rfl (by simpa using him.symm), hre⟩
  rw [lp.inner_eq_tsum]
  apply tsum_nonneg
  intro j
  cases j with
  | zero =>
      simp only [sub_apply, smul_apply,
        one_apply_eq_self, lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply,
        forwardShift_row_zero, sub_zero, inner_smul_left]
      exact mul_nonneg (by simpa using hc) (by rw [inner_self_eq_norm_sq_to_K]; positivity)
  | succ j =>
      simpa only [sub_apply, smul_apply,
        one_apply_eq_self, lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply,
        forwardShift_row_succ, ContinuousLinearMap.id_apply] using
          (hrow j).inner_nonneg_left (f (j+1))

end Kaplansky

end

noncomputable section
open scoped BigOperators
namespace Kaplansky
variable {n : ℕ} {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem block_norm_le_of_column (T : Fin n → E →L[ℂ] F)
    (hcol : ∑ i, (T i).adjoint.comp (T i) = ContinuousLinearMap.id ℂ E) (i : Fin n) :
    ‖T i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  have he : ∑ j, ‖T j v‖ ^ 2 = ‖v‖ ^ 2 := by
    have h := congrArg (fun W : E →L[ℂ] E => RCLike.re (inner ℂ v (W v))) hcol
    simpa only [sum_apply, ContinuousLinearMap.comp_apply,
      inner_sum, map_sum, ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearMap.id_apply, inner_self_eq_norm_sq] using h
  have hi : ‖T i v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [← he]
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖T j v‖) (Finset.mem_univ i)
  have hn := norm_nonneg v
  have hni := norm_nonneg (T i v)
  nlinarith

end Kaplansky

end

end OAI
