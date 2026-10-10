import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Order.Interval.Set.OrderIso
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

def periodicLiftFun (e : ℝ ≃o ℝ) (x : ℝ) : ℝ :=
  (⌊x⌋ : ℝ) + e (Int.fract x)

theorem periodicLiftFun_range (e : ℝ ≃o ℝ) (h0 : e 0 = 0) (h1 : e 1 = 1)
    (x : ℝ) : 0 ≤ e (Int.fract x) ∧ e (Int.fract x) < 1 := by
  constructor
  · simpa only [h0] using e.monotone (Int.fract_nonneg x)
  · simpa only [h1] using e.strictMono (Int.fract_lt_one x)

theorem periodicLiftFun_floor (e : ℝ ≃o ℝ) (h0 : e 0 = 0) (h1 : e 1 = 1)
    (x : ℝ) : ⌊periodicLiftFun e x⌋ = ⌊x⌋ := by
  apply Int.floor_eq_iff.mpr
  have hr := periodicLiftFun_range e h0 h1 x
  dsimp only [periodicLiftFun]
  constructor <;> linarith

theorem periodicLiftFun_fract (e : ℝ ≃o ℝ) (h0 : e 0 = 0) (h1 : e 1 = 1)
    (x : ℝ) : Int.fract (periodicLiftFun e x) = e (Int.fract x) := by
  rw [Int.fract, periodicLiftFun_floor e h0 h1]
  dsimp only [periodicLiftFun]
  ring

theorem periodicLiftFun_strictMono (e : ℝ ≃o ℝ) (h0 : e 0 = 0) (h1 : e 1 = 1) :
    StrictMono (periodicLiftFun e) := by
  intro x y hxy
  have hfloor : ⌊x⌋ ≤ ⌊y⌋ := Int.floor_mono hxy.le
  rcases hfloor.eq_or_lt with heq | hlt
  · have hfrac : Int.fract x < Int.fract y := by
      dsimp only [Int.fract]
      rw [heq]
      linarith
    have he := e.strictMono hfrac
    dsimp only [periodicLiftFun]
    rw [heq]
    linarith
  · have hgap : (⌊x⌋ : ℝ) + 1 ≤ (⌊y⌋ : ℝ) := by
      exact_mod_cast (Int.add_one_le_iff.mpr hlt)
    have hx := (periodicLiftFun_range e h0 h1 x).2
    have hy := (periodicLiftFun_range e h0 h1 y).1
    dsimp only [periodicLiftFun]
    linarith

theorem periodicLiftFun_rightInverse (e : ℝ ≃o ℝ) (h0 : e 0 = 0) (h1 : e 1 = 1) :
    Function.RightInverse (periodicLiftFun e.symm) (periodicLiftFun e) := by
  have h0' : e.symm 0 = 0 := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact h0.symm
  have h1' : e.symm 1 = 1 := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact h1.symm
  intro x
  unfold periodicLiftFun
  rw [show ⌊(⌊x⌋ : ℝ) + e.symm (Int.fract x)⌋ = ⌊x⌋ from
    periodicLiftFun_floor e.symm h0' h1' x]
  rw [show Int.fract ((⌊x⌋ : ℝ) + e.symm (Int.fract x)) = e.symm (Int.fract x) from
    periodicLiftFun_fract e.symm h0' h1' x]
  rw [e.apply_symm_apply, Int.floor_add_fract]

def unitPeriodicOrderIso (e : ℝ ≃o ℝ) (h0 : e 0 = 0) (h1 : e 1 = 1) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfRightInverse (periodicLiftFun e)
    (periodicLiftFun_strictMono e h0 h1) (periodicLiftFun e.symm)
    (periodicLiftFun_rightInverse e h0 h1)

@[simp] theorem unitPeriodicOrderIso_apply (e : ℝ ≃o ℝ) (h0 : e 0 = 0) (h1 : e 1 = 1)
    (x : ℝ) : unitPeriodicOrderIso e h0 h1 x = periodicLiftFun e x := rfl

@[simp] theorem unitPeriodicOrderIso_symm_apply (e : ℝ ≃o ℝ)
    (h0 : e 0 = 0) (h1 : e 1 = 1) (x : ℝ) :
    (unitPeriodicOrderIso e h0 h1).symm x = periodicLiftFun e.symm x := rfl

theorem periodicLiftFun_add_int (e : ℝ ≃o ℝ) (x : ℝ) (j : ℤ) :
    periodicLiftFun e (x + j) = periodicLiftFun e x + j := by
  simp only [periodicLiftFun, Int.floor_add_intCast, Int.fract_add_intCast, Int.cast_add]
  ring

theorem periodicLiftFun_int (e : ℝ ≃o ℝ) (h0 : e 0 = 0) (j : ℤ) :
    periodicLiftFun e j = j := by
  simp only [periodicLiftFun, Int.floor_intCast, Int.fract_intCast, h0, add_zero]

theorem periodicLiftFun_of_mem_Ico (e : ℝ ≃o ℝ) {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    periodicLiftFun e x = e x := by
  have hf : ⌊x⌋ = 0 := Int.floor_eq_zero_iff.mpr hx
  simp only [periodicLiftFun, Int.fract, hf, Int.cast_zero, sub_zero, zero_add]

def twoSlope (x : ℝ) : ℝ := if x ≤ 1 / 9 then 8 * x else (x + 7) / 8

def twoSlopeInverse (x : ℝ) : ℝ := if x ≤ 8 / 9 then x / 8 else 8 * x - 7

theorem twoSlope_strictMono : StrictMono twoSlope := by
  intro x y hxy
  unfold twoSlope
  split_ifs <;> linarith

theorem twoSlope_rightInverse : Function.RightInverse twoSlopeInverse twoSlope := by
  intro x
  by_cases hx : x ≤ 8 / 9
  · have hb : x / 8 ≤ 1 / 9 := by linarith
    simp only [twoSlopeInverse, ite_eq_left hx, twoSlope, ite_eq_left hb]
    ring
  · have hb : ¬8 * x - 7 ≤ 1 / 9 := by linarith
    simp only [twoSlopeInverse, ite_eq_right hx, twoSlope, ite_eq_right hb]
    ring

def twoSlopeOrderIso : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfRightInverse twoSlope twoSlope_strictMono
    twoSlopeInverse twoSlope_rightInverse

@[simp] theorem twoSlopeOrderIso_apply (x : ℝ) : twoSlopeOrderIso x = twoSlope x := rfl

@[simp] theorem twoSlopeOrderIso_symm_apply (x : ℝ) :
    twoSlopeOrderIso.symm x = twoSlopeInverse x := rfl

@[simp] theorem twoSlopeOrderIso_zero : twoSlopeOrderIso 0 = 0 := by
  norm_num [twoSlopeOrderIso_apply, twoSlope]

@[simp] theorem twoSlopeOrderIso_one : twoSlopeOrderIso 1 = 1 := by
  norm_num [twoSlopeOrderIso_apply, twoSlope]

def periodicBend : ℝ ≃o ℝ :=
  unitPeriodicOrderIso twoSlopeOrderIso twoSlopeOrderIso_zero twoSlopeOrderIso_one

theorem periodicBend_apply (x : ℝ) :
    periodicBend x = (⌊x⌋ : ℝ) + twoSlope (Int.fract x) := rfl

theorem periodicBend_symm_apply (x : ℝ) :
    periodicBend.symm x = (⌊x⌋ : ℝ) + twoSlopeInverse (Int.fract x) := rfl

theorem periodicBend_add_int (x : ℝ) (j : ℤ) :
    periodicBend (x + j) = periodicBend x + j :=
  periodicLiftFun_add_int twoSlopeOrderIso x j

theorem periodicBend_symm_add_int (x : ℝ) (j : ℤ) :
    periodicBend.symm (x + j) = periodicBend.symm x + j :=
  periodicLiftFun_add_int twoSlopeOrderIso.symm x j

@[simp] theorem periodicBend_int (j : ℤ) : periodicBend j = j :=
  periodicLiftFun_int twoSlopeOrderIso twoSlopeOrderIso_zero j

@[simp] theorem periodicBend_zero : periodicBend 0 = 0 := by
  simpa only [Int.cast_zero] using periodicBend_int 0

@[simp] theorem periodicBend_one : periodicBend 1 = 1 := by
  simpa only [Int.cast_one] using periodicBend_int 1

theorem periodicBend_eq_twoSlope {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    periodicBend x = twoSlope x := by
  rcases hx.2.eq_or_lt with heq | hlt
  · subst x
    norm_num [twoSlope]
  · exact periodicLiftFun_of_mem_Ico twoSlopeOrderIso ⟨hx.1, hlt⟩

@[simp] theorem periodicBend_ninth : periodicBend (1 / 9) = 8 / 9 := by
  rw [periodicBend_eq_twoSlope (by norm_num)]
  norm_num [twoSlope]

theorem periodicBend_displacement (x : ℝ) :
    0 ≤ periodicBend x - x ∧ periodicBend x - x ≤ 7 / 9 := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  have he : periodicBend x - x = twoSlope (Int.fract x) - Int.fract x := by
    rw [periodicBend_apply]
    have hf := Int.floor_add_fract x
    linarith
  rw [he]
  unfold twoSlope
  split_ifs <;> constructor <;> linarith

def translatedPeriodicOrderIso (a c : ℝ) : ℝ ≃o ℝ where
  toFun x := c + periodicBend (x - a)
  invFun y := a + periodicBend.symm (y - c)
  left_inv x := by simp only [add_sub_cancel_left, periodicBend.symm_apply_apply]; ring
  right_inv y := by simp only [add_sub_cancel_left, periodicBend.apply_symm_apply]; ring
  map_rel_iff' := by
    intro x y
    change c + periodicBend (x - a) ≤ c + periodicBend (y - a) ↔ x ≤ y
    simp only [add_le_add_iff_left, periodicBend.le_iff_le, sub_le_sub_iff_right]

theorem translatedPeriodicOrderIso_apply (a c x : ℝ) :
    translatedPeriodicOrderIso a c x = c + periodicBend (x - a) := rfl

theorem translatedPeriodicOrderIso_symm_apply (a c y : ℝ) :
    (translatedPeriodicOrderIso a c).symm y = a + periodicBend.symm (y - c) := rfl

theorem translatedPeriodicOrderIso_add_int (a c x : ℝ) (j : ℤ) :
    translatedPeriodicOrderIso a c (x + j) = translatedPeriodicOrderIso a c x + j := by
  change c + periodicBend (x + j - a) = c + periodicBend (x - a) + j
  rw [show x + (j : ℝ) - a = x - a + j by ring, periodicBend_add_int]
  ring

theorem translatedPeriodicOrderIso_symm_add_int (a c x : ℝ) (j : ℤ) :
    (translatedPeriodicOrderIso a c).symm (x + j) =
      (translatedPeriodicOrderIso a c).symm x + j := by
  change a + periodicBend.symm (x + j - c) = a + periodicBend.symm (x - c) + j
  rw [show x + (j : ℝ) - c = x - c + j by ring, periodicBend_symm_add_int]
  ring

@[simp] theorem translatedPeriodicOrderIso_start (a c : ℝ) :
    translatedPeriodicOrderIso a c a = c := by
  simp [translatedPeriodicOrderIso_apply]

theorem translatedPeriodicOrderIso_break (a c : ℝ) :
    translatedPeriodicOrderIso a c (a + 1 / 9) = c + 8 / 9 := by
  rw [translatedPeriodicOrderIso_apply, add_sub_cancel_left, periodicBend_ninth]

theorem translatedPeriodicOrderIso_end (a c : ℝ) :
    translatedPeriodicOrderIso a c (a + 1) = c + 1 := by
  simp [translatedPeriodicOrderIso_apply]

theorem translatedPeriodicOrderIso_displacement (a c x : ℝ) :
    c - a ≤ translatedPeriodicOrderIso a c x - x ∧
      translatedPeriodicOrderIso a c x - x ≤ c - a + 7 / 9 := by
  have h := periodicBend_displacement (x - a)
  rw [translatedPeriodicOrderIso_apply]
  constructor <;> linarith

theorem translatedPeriodicOrderIso_left (a c x : ℝ)
    (hx : x ∈ Set.Icc a (a + 1 / 9)) :
    translatedPeriodicOrderIso a c x = c + 8 * (x - a) := by
  have hu : x - a ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  rw [translatedPeriodicOrderIso_apply, periodicBend_eq_twoSlope hu, twoSlope,
    ite_eq_left (by linarith [hx.2])]

theorem translatedPeriodicOrderIso_right (a c x : ℝ)
    (hx : x ∈ Set.Icc (a + 1 / 9) (a + 1)) :
    translatedPeriodicOrderIso a c x = c + 8 / 9 + (x - a - 1 / 9) / 8 := by
  have hu : x - a ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  rw [translatedPeriodicOrderIso_apply, periodicBend_eq_twoSlope hu]
  unfold twoSlope
  split_ifs <;> linarith [hx.1]

theorem translatedPeriodicOrderIso_inverse_left (a c y : ℝ)
    (hy : y ∈ Set.Icc c (c + 8 / 9)) :
    (translatedPeriodicOrderIso a c).symm y = a + (y - c) / 8 := by
  apply (translatedPeriodicOrderIso a c).injective
  rw [(translatedPeriodicOrderIso a c).apply_symm_apply,
    translatedPeriodicOrderIso_left a c _ (by constructor <;> linarith [hy.1, hy.2])]
  ring

theorem translatedPeriodicOrderIso_inverse_right (a c y : ℝ)
    (hy : y ∈ Set.Icc (c + 8 / 9) (c + 1)) :
    (translatedPeriodicOrderIso a c).symm y = a + 1 / 9 + 8 * (y - c - 8 / 9) := by
  apply (translatedPeriodicOrderIso a c).injective
  rw [(translatedPeriodicOrderIso a c).apply_symm_apply,
    translatedPeriodicOrderIso_right a c _ (by constructor <;> linarith [hy.1, hy.2])]
  ring

end MarkovSuperreflexivity

end

end OAI
