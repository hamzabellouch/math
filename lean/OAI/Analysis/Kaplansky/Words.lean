import OAI.Analysis.Kaplansky.Shift
import OAI.Geometry.ComplexBundle.Tuples
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Submodule.Basic

namespace OAI

/-! Word propagation through Hilbert shifts and normalized tuple operators. -/

namespace Kaplansky
open scoped BigOperators
variable {𝕜 V ι : Type*} [Semiring 𝕜] [AddCommMonoid V] [Module 𝕜 V]

/-- Apply a word of operators, in the multiplication order used by
noncommutative polynomials. A generator and its adjoint are separate
letters of the alphabet. -/
def applyWord (T : ι → Module.End 𝕜 V) : List ι → V → V
  | [], v => v
  | a::w, v => T a (applyWord T w v)

theorem word_mem_level (T : ι → Module.End 𝕜 V) (F : ℕ → Submodule 𝕜 V)
    (hstep : ∀ a k v, v ∈ F k → T a v ∈ F (k+1))
    (w : List ι) (k : ℕ) {v : V} (hv : v ∈ F k) :
    applyWord T w v ∈ F (k+w.length) := by
  induction w with
  | nil => simpa [applyWord] using hv
  | cons a w ih => simpa [applyWord, Nat.add_assoc] using hstep a (k+w.length) _ ih

theorem polynomial_mem_level (T : ι → Module.End 𝕜 V) (F : ℕ → Submodule 𝕜 V)
    (hmono : Monotone F) (hstep : ∀ a k v, v ∈ F k → T a v ∈ F (k+1))
    {κ : Type*} (s : Finset κ) (words : κ → List ι) (coeff : κ → 𝕜) (R : ℕ)
    (hdeg : ∀ j ∈ s, (words j).length ≤ R) {v : V} (hv : v ∈ F 0) :
    (∑ j ∈ s, coeff j • applyWord T (words j) v) ∈ F R := by
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  apply hmono (hdeg j hj)
  simpa using word_mem_level T F hstep (words j) 0 hv

end Kaplansky

noncomputable section
open scoped BigOperators
namespace Kaplansky
variable {E : ℕ → Type*} [∀ j, NormedAddCommGroup (E j)]
  [∀ j, InnerProductSpace ℂ (E j)] [∀ j, CompleteSpace (E j)]

/-- The actual first k+1 levels of the Hilbert sum. -/
def hilbertLevels (k : ℕ) : Submodule ℂ (FiberHilbertSum E) where
  carrier := {f | ∀ j, k < j → f j = 0}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg j hj; simp [hf j hj, hg j hj]
  smul_mem' := by intro c f hf j hj; simp [hf j hj]

omit [∀ j, CompleteSpace (E j)] in
theorem hilbertLevels_mono : Monotone (hilbertLevels (E := E)) := by
  intro k l h f hf j hj
  exact hf j (lt_of_le_of_lt h hj)

variable {n : ℕ} (T : Fin n → ∀ j, E j →L[ℂ] E (j+1)) (hT : ∀ i j, ‖T i j‖ ≤ 1)

/-- False letters are generators; true letters are their actual adjoints. -/
def shiftLetter (a : Bool × Fin n) : Module.End ℂ (FiberHilbertSum E) :=
  if a.1 then (forwardShift (T a.2) (hT a.2)).adjoint.toLinearMap
  else (forwardShift (T a.2) (hT a.2)).toLinearMap

theorem shiftLetter_mem_level (a : Bool × Fin n) (k : ℕ) (f : FiberHilbertSum E)
    (hf : f ∈ hilbertLevels k) : shiftLetter T hT a f ∈ hilbertLevels (k+1) := by
  intro j hj
  rcases a with ⟨b,i⟩
  cases b with
  | false =>
      cases j with
      | zero => omega
      | succ j =>
          change forwardShift (T i) (hT i) f (j+1) = 0
          rw [forwardShift_apply_succ, hf j (by omega), map_zero]
  | true =>
      change (forwardShift (T i) (hT i)).adjoint f j = 0
      rw [forwardShift_adjoint_apply, hf (j+1) (by omega), map_zero]

theorem shift_word_from_bottom (w : List (Bool × Fin n)) (v : E 0) :
    applyWord (shiftLetter T hT) w (lp.single 2 0 v) ∈ hilbertLevels w.length := by
  have hv : lp.single 2 0 v ∈ hilbertLevels 0 := by
    intro j hj
    simp [Pi.single_eq_of_ne (show j ≠ 0 by omega)]
  simpa using word_mem_level (shiftLetter T hT) hilbertLevels (shiftLetter_mem_level T hT) w 0 hv

/-- Actual operator *-polynomials of degree R send the bottom fiber into
levels zero through R; no global Hilbert-bundle trivialization is assumed. -/
theorem shift_polynomial_from_bottom {K : Type*} (s : Finset K)
    (words : K → List (Bool × Fin n)) (coeff : K → ℂ) (R : ℕ)
    (hdeg : ∀ j ∈ s, (words j).length ≤ R) (v : E 0) :
    (∑ j ∈ s, coeff j • applyWord (shiftLetter T hT) (words j) (lp.single 2 0 v)) ∈
      hilbertLevels R := by
  apply polynomial_mem_level (shiftLetter T hT) hilbertLevels hilbertLevels_mono
    (shiftLetter_mem_level T hT) s words coeff R hdeg
  intro j hj
  simp [Pi.single_eq_of_ne (show j ≠ 0 by omega)]

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder
namespace Kaplansky.NormalizedHermitianTuple
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

local instance : CompleteSpace E := FiniteDimensional.complete ℂ E
local instance : CompleteSpace F := FiniteDimensional.complete ℂ F

/-- Actual bounded operators on the finite-dimensional Hilbert fibers. -/
def operator (T : NormalizedHermitianTuple E F) (i : Fin 24) : E →L[ℂ] F :=
  (T.forward i).toContinuousLinearMap

theorem operator_adjoint (T : NormalizedHermitianTuple E F) (i : Fin 24) :
    (T.operator i).adjoint = (T.reverse i).toContinuousLinearMap := by
  ext w
  apply ext_inner_right ℂ
  intro v
  exact (ContinuousLinearMap.adjoint_inner_left (T.operator i) v w).trans (T.adjoint_inner i v w).symm

theorem operator_column (T : NormalizedHermitianTuple E F) :
    ∑ i, (T.operator i).adjoint.comp (T.operator i) = ContinuousLinearMap.id ℂ E := by
  simp_rw [operator_adjoint]
  ext v
  exact congrArg (fun a : E →ₗ[ℂ] E => a v) T.column

theorem operator_row (T : NormalizedHermitianTuple E F) :
    ((2/3 : ℂ) • ContinuousLinearMap.id ℂ F -
      ∑ i, (T.operator i).comp (T.operator i).adjoint).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
  intro w
  simp_rw [operator_adjoint]
  let A : F →ₗ[ℂ] F := (2/3 : ℂ) • LinearMap.id - ∑ i, (T.forward i).comp (T.reverse i)
  have h : 0 ≤ inner ℂ w (A w) := T.row w
  rcases RCLike.nonneg_iff.mp h with ⟨hre,him⟩
  change (inner ℂ w (A w)).im = 0 at him
  have he : inner ℂ (A w) w = inner ℂ w (A w) := by
    rw [← inner_conj_symm]
    apply Complex.ext
    · rfl
    · change -(inner ℂ w (A w)).im = (inner ℂ w (A w)).im
      rw [him,neg_zero]
  change (↑((inner ℂ (A w) w).re) = inner ℂ (A w) w) ∧ 0 ≤ (inner ℂ (A w) w).re
  rw [he]
  exact ⟨Complex.ext rfl (by simpa using him.symm),hre⟩

theorem operator_norm_le (T : NormalizedHermitianTuple E F) (i : Fin 24) : ‖T.operator i‖ ≤ 1 :=
  Kaplansky.block_norm_le_of_column T.operator T.operator_column i

end Kaplansky.NormalizedHermitianTuple

end

end OAI
