import OAI.GroupTheory.PolycyclicRecognition.Algebra.UnitaryLazyEnergy
import Mathlib.Analysis.InnerProductSpace.l2Space

namespace OAI

/-! # The real regular Hilbert representation

This is the actual square-summable function space on the group, with explicit
coordinate formulas for translation and the Dirac vector.
-/
noncomputable section
namespace PolycyclicRecognition
open scoped ENNReal

abbrev RegularHilbert (G : Type*) := lp (fun _ : G => ℝ) 2

def regularHilbertEvaluation {ι : Type*} (x : ι) : RegularHilbert ι →ₗ[ℝ] ℝ where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem regularHilbert_sum_apply {ι J : Type*} (A : Finset J)
    (f : J → RegularHilbert ι) (x : ι) : (∑ j ∈ A, f j) x = ∑ j ∈ A, f j x :=
  map_sum (regularHilbertEvaluation x) f A

theorem regularHilbert_add_apply {ι : Type*} (f h : RegularHilbert ι) (x : ι) :
    (f + h) x = f x + h x := rfl

theorem regularHilbert_smul_apply {ι : Type*} (c : ℝ) (f : RegularHilbert ι) (x : ι) :
    (c • f) x = c * f x := rfl

def hilbertReindexVector {ι : Type*} (e : ι ≃ ι) (f : RegularHilbert ι) : RegularHilbert ι :=
  ⟨fun x => f (e x), memℓp_gen
    (e.summable_iff.mpr ((lp.memℓp f).summable (by norm_num)))⟩

theorem hilbertReindexVector_inner {ι : Type*} (e : ι ≃ ι) (f h : RegularHilbert ι) :
    inner ℝ (hilbertReindexVector e f) (hilbertReindexVector e h) = inner ℝ f h := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  change (∑' x, inner ℝ (f (e x)) (h (e x))) = ∑' x, inner ℝ (f x) (h x)
  exact e.tsum_eq (fun x => inner ℝ (f x) (h x))

theorem hilbertReindexVector_norm {ι : Type*} (e : ι ≃ ι) (f : RegularHilbert ι) :
    ‖hilbertReindexVector e f‖ = ‖f‖ := by
  have he : ‖hilbertReindexVector e f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      hilbertReindexVector_inner]
  nlinarith [norm_nonneg f, norm_nonneg (hilbertReindexVector e f)]

def hilbertReindex {ι : Type*} (e : ι ≃ ι) :
    RegularHilbert ι ≃ₗᵢ[ℝ] RegularHilbert ι where
  toFun := hilbertReindexVector e
  invFun := hilbertReindexVector e.symm
  left_inv f := by ext x; exact congrArg f (e.apply_symm_apply x)
  right_inv f := by ext x; exact congrArg f (e.symm_apply_apply x)
  map_add' f h := by ext x; rfl
  map_smul' c f := by ext x; rfl
  norm_map' := hilbertReindexVector_norm e

@[simp] theorem hilbertReindex_apply {ι : Type*} (e : ι ≃ ι)
    (f : RegularHilbert ι) (x : ι) : hilbertReindex e f x = f (e x) := rfl

variable {G : Type*} [Group G]

def regularHilbertRepresentation : G →* (RegularHilbert G ≃ₗᵢ[ℝ] RegularHilbert G) where
  toFun g := hilbertReindex (Equiv.mulLeft g⁻¹)
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [mul_inv_rev]

@[simp] theorem regularHilbertRepresentation_apply (g : G) (f : RegularHilbert G) (x : G) :
    regularHilbertRepresentation g f x = f (g⁻¹ * x) := rfl

def regularDirac [DecidableEq G] : RegularHilbert G := lp.single 2 1 1

@[simp] theorem regularDirac_apply [DecidableEq G] (x : G) :
    regularDirac (G := G) x = if x = 1 then 1 else 0 := by
  simp [regularDirac, lp.single_apply, Pi.single_apply]

theorem regularHilbert_inner_dirac [DecidableEq G] (f : RegularHilbert G) (g : G) :
    inner ℝ f (regularHilbertRepresentation g regularDirac) = f g := by
  have he : regularHilbertRepresentation g (regularDirac (G := G)) = lp.single 2 g 1 := by
    ext x
    simp [lp.single_apply, Pi.single_apply, inv_mul_eq_one, eq_comm]
  rw [he, lp.inner_single_right]
  simp

omit [Group G] in
theorem regularHilbert_apply_le_norm (f : RegularHilbert G) (g : G) : |f g| ≤ ‖f‖ := by
  simpa only [Real.norm_eq_abs] using lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) f g

end PolycyclicRecognition

end

end OAI
