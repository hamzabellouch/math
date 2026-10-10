import Mathlib

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
namespace YauCounterexamples
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

abbrev RealForm (V : Type*) [AddCommGroup V] [Module ℝ V] :=
  LinearMap.BilinForm ℝ V

def innerForm : RealForm V :=
  LinearMap.mk₂ ℝ (inner ℝ)
    (fun _ _ _ => inner_add_left _ _ _)
    (fun _ _ _ => real_inner_smul_left _ _ _)
    (fun _ _ _ => inner_add_right _ _ _)
    (fun _ _ _ => real_inner_smul_right _ _ _)

@[simp] theorem innerForm_apply (x y : V) : innerForm x y = inner ℝ x y := rfl

theorem innerForm_isSymm : (innerForm : RealForm V).IsSymm :=
  ⟨fun x y => real_inner_comm y x⟩

def StrictlyBelow (U H : RealForm V) : Prop :=
  ∀ x : V, x ≠ 0 → U x x < H x x

structure AdmissiblePhaseHessian (H : RealForm V) (a b : V) where
  realPart : RealForm V
  imagPart : RealForm V
  real_symm : realPart.IsSymm
  imag_symm : imagPart.IsSymm
  column_b : ∀ x, imagPart b x = realPart a x
  column_a : ∀ x, imagPart a x = -realPart b x
  gap : StrictlyBelow realPart H

def completePhaseColumns (U : RealForm V) (a b : V) : RealForm V :=
  let l := innerForm a
  let m := innerForm b
  let A := inner ℝ a a
  let B := inner ℝ b b
  show RealForm V from
  -(A⁻¹ • (l.smulRight (U b) + (U b).smulRight l)) +
    B⁻¹ • (m.smulRight (U a) + (U a).smulRight m) +
    (U a b / A ^ 2) • l.smulRight l -
    (U a b / B ^ 2) • m.smulRight m -
    (U a a / (A * B)) • (l.smulRight m + m.smulRight l)

@[simp] theorem completePhaseColumns_apply (U : RealForm V) (a b x y : V) :
    completePhaseColumns U a b x y =
      -(inner ℝ a a)⁻¹ * (inner ℝ a x * U b y + U b x * inner ℝ a y) +
      (inner ℝ b b)⁻¹ * (inner ℝ b x * U a y + U a x * inner ℝ b y) +
      U a b / (inner ℝ a a) ^ 2 * (inner ℝ a x * inner ℝ a y) -
      U a b / (inner ℝ b b) ^ 2 * (inner ℝ b x * inner ℝ b y) -
      U a a / (inner ℝ a a * inner ℝ b b) *
        (inner ℝ a x * inner ℝ b y + inner ℝ b x * inner ℝ a y) := by
  simp only [completePhaseColumns, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
    innerForm_apply, smul_eq_mul]
  ring

theorem completePhaseColumns_isSymm (U : RealForm V) (a b : V) :
    (completePhaseColumns U a b).IsSymm := by
  constructor
  intro x y
  simp only [completePhaseColumns_apply]
  ring

theorem completePhaseColumns_column_a (U : RealForm V) (hU : U.IsSymm)
    (a b : V) (ha : a ≠ 0) (hb : b ≠ 0) (hab : inner ℝ a b = 0)
    (x : V) :
    completePhaseColumns U a b a x = -U b x := by
  have ha2 : inner ℝ a a ≠ 0 := ne_of_gt (real_inner_self_pos.mpr ha)
  have hb2 : inner ℝ b b ≠ 0 := ne_of_gt (real_inner_self_pos.mpr hb)
  have hba : inner ℝ b a = 0 := by rw [real_inner_comm, hab]
  rw [completePhaseColumns_apply, hba, hU.eq b a]
  simp only [zero_mul, zero_add, mul_zero]
  field_simp
  ring

theorem completePhaseColumns_column_b (U : RealForm V) (a b : V)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : inner ℝ a b = 0)
    (htrace : U a a + U b b = 0) (x : V) :
    completePhaseColumns U a b b x = U a x := by
  have ha2 : inner ℝ a a ≠ 0 := ne_of_gt (real_inner_self_pos.mpr ha)
  have hb2 : inner ℝ b b ≠ 0 := ne_of_gt (real_inner_self_pos.mpr hb)
  have huu : U b b = -U a a := by linarith
  rw [completePhaseColumns_apply, hab, huu]
  simp only [zero_mul, zero_add, mul_zero]
  field_simp
  ring

def admissibleNoncritical (H : RealForm V) (hH : H.IsSymm)
    (a b : V) (ha : a ≠ 0) (hb : b ≠ 0) (hab : inner ℝ a b = 0)
    (hstrict : 0 < H a a + H b b) : AdmissiblePhaseHessian H a b := by
  let α := (H a a + H b b) / (inner ℝ a a + inner ℝ b b)
  have hden : 0 < inner ℝ a a + inner ℝ b b :=
    add_pos (real_inner_self_pos.mpr ha) (real_inner_self_pos.mpr hb)
  have hα : 0 < α := div_pos hstrict hden
  let U : RealForm V := H - α • innerForm
  have hU : U.IsSymm := hH.sub (innerForm_isSymm.smul α)
  have htrace : U a a + U b b = 0 := by
    change (H a a - α * inner ℝ a a) + (H b b - α * inner ℝ b b) = 0
    dsimp [α]
    field_simp
    ring
  exact {
    realPart := U
    imagPart := completePhaseColumns U a b
    real_symm := hU
    imag_symm := completePhaseColumns_isSymm U a b
    column_b := completePhaseColumns_column_b U a b ha hb hab htrace
    column_a := completePhaseColumns_column_a U hU a b ha hb hab
    gap := by
      intro x hx
      change H x x - α * inner ℝ x x < H x x
      exact sub_lt_self _ (mul_pos hα (real_inner_self_pos.mpr hx)) }

def phaseCriticalProjection (H : RealForm V) (b : V) : V →ₗ[ℝ] V :=
  LinearMap.id - (H b b)⁻¹ • (H b).smulRight b

@[simp] theorem phaseCriticalProjection_apply (H : RealForm V) (b x : V) :
    phaseCriticalProjection H b x = x - ((H b b)⁻¹ * H b x) • b := by
  simp [phaseCriticalProjection, smul_smul]

theorem phaseCriticalProjection_self (H : RealForm V) (b : V) (hb : H b b ≠ 0) :
    phaseCriticalProjection H b b = 0 := by
  simp [hb]

def phaseCriticalCorrection (H : RealForm V) (b : V) : RealForm V :=
  (H b b)⁻¹ • (H b).smulRight (H b) +
    innerForm.compl₁₂ (phaseCriticalProjection H b) (phaseCriticalProjection H b)

@[simp] theorem phaseCriticalCorrection_apply (H : RealForm V) (b x y : V) :
    phaseCriticalCorrection H b x y = (H b b)⁻¹ * (H b x * H b y) +
      inner ℝ (phaseCriticalProjection H b x) (phaseCriticalProjection H b y) := rfl

theorem phaseCriticalCorrection_isSymm (H : RealForm V) (b : V) :
    (phaseCriticalCorrection H b).IsSymm := by
  constructor
  intro x y
  simp only [phaseCriticalCorrection_apply]
  rw [real_inner_comm (phaseCriticalProjection H b y) (phaseCriticalProjection H b x)]
  ring

theorem phaseCriticalCorrection_pos (H : RealForm V) (b : V) (hb : 0 < H b b)
    (x : V) (hx : x ≠ 0) : 0 < phaseCriticalCorrection H b x x := by
  rw [phaseCriticalCorrection_apply]
  by_cases hbx : H b x = 0
  · simpa [phaseCriticalProjection_apply, hbx] using real_inner_self_pos.mpr hx
  · have hfirst : 0 < (H b b)⁻¹ * (H b x * H b x) :=
      mul_pos (inv_pos.mpr hb) (mul_self_pos.mpr hbx)
    exact add_pos_of_pos_of_nonneg hfirst (real_inner_self_nonneg)

theorem phaseCriticalCorrection_column (H : RealForm V) (b : V) (hb : H b b ≠ 0)
    (x : V) : phaseCriticalCorrection H b b x = H b x := by
  rw [phaseCriticalCorrection_apply, phaseCriticalProjection_self H b hb]
  simp [hb]

def admissibleCritical (H : RealForm V) (hH : H.IsSymm)
    (b : V) (hb : 0 < H b b) : AdmissiblePhaseHessian H 0 b := by
  let U := H - phaseCriticalCorrection H b
  have hUb (x : V) : U b x = 0 := by
    change H b x - phaseCriticalCorrection H b b x = 0
    rw [phaseCriticalCorrection_column H b (ne_of_gt hb), sub_self]
  exact {
    realPart := U
    imagPart := 0
    real_symm := hH.sub (phaseCriticalCorrection_isSymm H b)
    imag_symm := ⟨by simp⟩
    column_b := by intro x; simp
    column_a := by intro x; simp [hUb]
    gap := by
      intro x hx
      change H x x - phaseCriticalCorrection H b x x < H x x
      exact sub_lt_self _ (phaseCriticalCorrection_pos H b hb x hx) }

theorem phase_hessian_exists (H : RealForm V) (hH : H.IsSymm)
    (a b : V) (hab : inner ℝ a b = 0)
    (hsize : inner ℝ b b = 1 + inner ℝ a a)
    (hstrict : 0 < H a a + H b b) : Nonempty (AdmissiblePhaseHessian H a b) := by
  by_cases ha : a = 0
  · subst a
    have hb : 0 < H b b := by simpa using hstrict
    exact ⟨admissibleCritical H hH b hb⟩
  · have hb : b ≠ 0 := by
      intro h
      subst b
      simp only [inner_zero_left] at hsize
      have := real_inner_self_nonneg (x := a)
      linarith
    exact ⟨admissibleNoncritical H hH a b ha hb hab hstrict⟩
end YauCounterexamples
end

end OAI
