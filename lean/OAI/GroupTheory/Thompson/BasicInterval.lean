import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Basic dyadic intervals

A cell records its actual depth and its index on that dyadic grid.  Its
endpoints determine the record uniquely.  Composition is the affine image of
one cell inside another; no formal interval identifications are assumed.
-/

noncomputable section

namespace ThompsonNonamenability

structure BasicInterval where
  depth : ℕ
  index : Fin (2 ^ depth)
  deriving DecidableEq

namespace BasicInterval

@[ext] theorem ext_depth_index {I J : BasicInterval}
    (hd : I.depth = J.depth) (hi : I.index.val = J.index.val) : I = J := by
  cases I with
  | mk d i =>
    cases J with
    | mk e j =>
      dsimp at hd hi
      subst e
      have hij : i = j := Fin.ext hi
      subst j
      rfl

def left (I : BasicInterval) : ℝ := (I.index.val : ℝ) / (2 : ℝ) ^ I.depth

def right (I : BasicInterval) : ℝ := ((I.index.val : ℝ) + 1) / (2 : ℝ) ^ I.depth

def length (I : BasicInterval) : ℝ := ((2 : ℝ) ^ I.depth)⁻¹

def carrier (I : BasicInterval) : Set ℝ := Set.Icc I.left I.right

def interior (I : BasicInterval) : Set ℝ := Set.Ioo I.left I.right

def Internal (I : BasicInterval) : Prop := 0 < I.left ∧ I.right < 1

def Before (I J : BasicInterval) : Prop := I.right < J.left

def Contained (K I : BasicInterval) : Prop := I.left ≤ K.left ∧ K.right ≤ I.right

def chart (I : BasicInterval) (x : ℝ) : ℝ :=
  ((I.index.val : ℝ) + x) / (2 : ℝ) ^ I.depth

theorem denominator_pos (I : BasicInterval) : 0 < (2 : ℝ) ^ I.depth :=
  pow_pos (by norm_num) _

theorem denominator_ne_zero (I : BasicInterval) : (2 : ℝ) ^ I.depth ≠ 0 :=
  ne_of_gt I.denominator_pos

theorem length_pos (I : BasicInterval) : 0 < I.length :=
  inv_pos.mpr I.denominator_pos

theorem length_eq_right_sub_left (I : BasicInterval) :
    I.length = I.right - I.left := by
  unfold length right left
  ring

theorem left_nonneg (I : BasicInterval) : 0 ≤ I.left :=
  div_nonneg (Nat.cast_nonneg _) (le_of_lt I.denominator_pos)

theorem right_le_one (I : BasicInterval) : I.right ≤ 1 := by
  apply (div_le_one I.denominator_pos).2
  exact_mod_cast Nat.succ_le_of_lt I.index.isLt

theorem left_lt_right (I : BasicInterval) : I.left < I.right := by
  apply (div_lt_div_iff_of_pos_right I.denominator_pos).2
  linarith

theorem carrier_subset_unit (I : BasicInterval) : I.carrier ⊆ Set.Icc (0 : ℝ) 1 := by
  intro x hx
  exact ⟨I.left_nonneg.trans hx.1, hx.2.trans I.right_le_one⟩

theorem interior_subset_carrier (I : BasicInterval) : I.interior ⊆ I.carrier := by
  intro x hx
  exact ⟨hx.1.le, hx.2.le⟩

theorem interior_nonempty (I : BasicInterval) : I.interior.Nonempty := by
  exact ⟨(I.left + I.right) / 2, by
    constructor <;> linarith [I.left_lt_right]⟩

theorem contained_refl (I : BasicInterval) : I.Contained I := ⟨le_rfl, le_rfl⟩

theorem Contained.trans {I J K : BasicInterval}
    (hIJ : I.Contained J) (hJK : J.Contained K) : I.Contained K :=
  ⟨hJK.1.trans hIJ.1, hIJ.2.trans hJK.2⟩

theorem Contained.carrier_subset {I J : BasicInterval}
    (h : I.Contained J) : I.carrier ⊆ J.carrier := by
  intro x hx
  exact ⟨h.1.trans hx.1, hx.2.trans h.2⟩

theorem Contained.interior_subset {I J : BasicInterval}
    (h : I.Contained J) : I.interior ⊆ J.interior := by
  intro x hx
  exact ⟨h.1.trans_lt hx.1, hx.2.trans_le h.2⟩

theorem length_le_of_contained {I J : BasicInterval} (h : I.Contained J) :
    I.length ≤ J.length := by
  rw [length_eq_right_sub_left, length_eq_right_sub_left]
  exact sub_le_sub h.2 h.1

@[simp] theorem chart_zero (I : BasicInterval) : I.chart 0 = I.left := by
  simp [chart, left]

@[simp] theorem chart_one (I : BasicInterval) : I.chart 1 = I.right := rfl

theorem chart_eq_left_add_length_mul (I : BasicInterval) (x : ℝ) :
    I.chart x = I.left + I.length * x := by
  unfold chart left length
  ring

theorem chart_strictMono (I : BasicInterval) : StrictMono I.chart := by
  intro x y hxy
  apply (div_lt_div_iff_of_pos_right I.denominator_pos).2
  exact add_lt_add_right hxy _

theorem chart_injective (I : BasicInterval) : Function.Injective I.chart :=
  I.chart_strictMono.injective

theorem chart_mem_self_carrier_iff (I : BasicInterval) (x : ℝ) :
    I.chart x ∈ I.carrier ↔ x ∈ Set.Icc (0 : ℝ) 1 := by
  change I.left ≤ I.chart x ∧ I.chart x ≤ I.right ↔ 0 ≤ x ∧ x ≤ 1
  rw [← I.chart_zero, ← I.chart_one]
  simp only [I.chart_strictMono.le_iff_le]

theorem chart_mem_self_interior_iff (I : BasicInterval) (x : ℝ) :
    I.chart x ∈ I.interior ↔ x ∈ Set.Ioo (0 : ℝ) 1 := by
  change I.left < I.chart x ∧ I.chart x < I.right ↔ 0 < x ∧ x < 1
  rw [← I.chart_zero, ← I.chart_one]
  simp only [I.chart_strictMono.lt_iff_lt]

theorem ext_endpoints {I J : BasicInterval}
    (hl : I.left = J.left) (hr : I.right = J.right) : I = J := by
  have hlen : I.length = J.length := by
    rw [length_eq_right_sub_left, length_eq_right_sub_left, hl, hr]
  have hp : (2 : ℝ) ^ I.depth = (2 : ℝ) ^ J.depth := inv_injective hlen
  have hd : I.depth = J.depth :=
    (pow_right_inj₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)).1 hp
  apply ext_depth_index hd
  have hdiv : (I.index.val : ℝ) / (2 : ℝ) ^ J.depth =
      (J.index.val : ℝ) / (2 : ℝ) ^ J.depth := by
    simpa only [left, hd] using hl
  have hi : (I.index.val : ℝ) = (J.index.val : ℝ) :=
    (div_left_inj' J.denominator_ne_zero).1 hdiv
  exact_mod_cast hi

def root : BasicInterval := ⟨0, ⟨0, by norm_num⟩⟩

@[simp] theorem root_depth : root.depth = 0 := rfl

@[simp] theorem root_index : root.index.val = 0 := rfl

@[simp] theorem root_left : root.left = 0 := by norm_num [root, left]

@[simp] theorem root_right : root.right = 1 := by norm_num [root, right]

@[simp] theorem root_length : root.length = 1 := by norm_num [root, length]

@[simp] theorem root_chart (x : ℝ) : root.chart x = x := by simp [root, chart]

def comp (I J : BasicInterval) : BasicInterval where
  depth := I.depth + J.depth
  index := ⟨I.index.val * 2 ^ J.depth + J.index.val, by
    have hI : I.index.val + 1 ≤ 2 ^ I.depth := Nat.succ_le_of_lt I.index.isLt
    calc
      I.index.val * 2 ^ J.depth + J.index.val <
          I.index.val * 2 ^ J.depth + 2 ^ J.depth := Nat.add_lt_add_left J.index.isLt _
      _ = (I.index.val + 1) * 2 ^ J.depth := by ring
      _ ≤ 2 ^ I.depth * 2 ^ J.depth := Nat.mul_le_mul_right _ hI
      _ = 2 ^ (I.depth + J.depth) := (pow_add _ _ _).symm⟩

@[simp] theorem comp_depth (I J : BasicInterval) : (I.comp J).depth = I.depth + J.depth := rfl

@[simp] theorem comp_index (I J : BasicInterval) :
    (I.comp J).index.val = I.index.val * 2 ^ J.depth + J.index.val := rfl

theorem chart_comp (I J : BasicInterval) (x : ℝ) :
    (I.comp J).chart x = I.chart (J.chart x) := by
  simp only [chart, comp_depth, comp_index, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat, pow_add]
  field_simp
  ring

theorem left_comp (I J : BasicInterval) : (I.comp J).left = I.chart J.left := by
  rw [← chart_zero, chart_comp, chart_zero]

theorem right_comp (I J : BasicInterval) : (I.comp J).right = I.chart J.right := by
  rw [← chart_one, chart_comp, chart_one]

theorem comp_assoc (I J K : BasicInterval) : (I.comp J).comp K = I.comp (J.comp K) := by
  apply ext_depth_index
  · simp only [comp_depth, Nat.add_assoc]
  · simp only [comp_index, comp_depth, pow_add]
    ring

@[simp] theorem comp_root (I : BasicInterval) : I.comp root = I := by
  apply ext_depth_index <;> simp

@[simp] theorem root_comp (I : BasicInterval) : root.comp I = I := by
  apply ext_depth_index <;> simp

theorem comp_left_injective (I : BasicInterval) : Function.Injective I.comp := by
  intro J K h
  have hd : J.depth = K.depth := Nat.add_left_cancel (congrArg depth h)
  apply ext_depth_index hd
  have hi := congrArg (fun C : BasicInterval => C.index.val) h
  simp only [comp_index, hd] at hi
  exact Nat.add_left_cancel hi

theorem comp_injective (I : BasicInterval) : Function.Injective I.comp :=
  comp_left_injective I

theorem comp_contained (I J : BasicInterval) : (I.comp J).Contained I := by
  constructor
  · rw [left_comp, ← I.chart_zero]
    exact I.chart_strictMono.monotone J.left_nonneg
  · rw [right_comp, ← I.chart_one]
    exact I.chart_strictMono.monotone J.right_le_one

theorem chart_mem_carrier_iff (I J : BasicInterval) (x : ℝ) :
    I.chart x ∈ (I.comp J).carrier ↔ x ∈ J.carrier := by
  simp only [carrier, Set.mem_Icc, left_comp, right_comp, I.chart_strictMono.le_iff_le]

theorem chart_mem_interior_iff (I J : BasicInterval) (x : ℝ) :
    I.chart x ∈ (I.comp J).interior ↔ x ∈ J.interior := by
  simp only [interior, Set.mem_Ioo, left_comp, right_comp, I.chart_strictMono.lt_iff_lt]

theorem comp_contained_iff (I J K : BasicInterval) :
    (I.comp J).Contained (I.comp K) ↔ J.Contained K := by
  simp only [Contained, left_comp, right_comp, I.chart_strictMono.le_iff_le]

theorem comp_internal_of_internal_right (I J : BasicInterval) (hJ : J.Internal) :
    (I.comp J).Internal := by
  constructor
  · rw [left_comp]
    have h := I.chart_strictMono hJ.1
    rw [chart_zero] at h
    exact I.left_nonneg.trans_lt h
  · rw [right_comp]
    have h := I.chart_strictMono hJ.2
    rw [chart_one] at h
    exact h.trans_le I.right_le_one

theorem comp_internal (I J : BasicInterval) (_hI : I.Internal) (hJ : J.Internal) :
    (I.comp J).Internal := comp_internal_of_internal_right I J hJ

theorem comp_before_comp (I : BasicInterval) {J K : BasicInterval} (h : J.Before K) :
    (I.comp J).Before (I.comp K) := by
  change (I.comp J).right < (I.comp K).left
  rw [right_comp, left_comp]
  exact I.chart_strictMono h

end BasicInterval

end ThompsonNonamenability

end

end OAI
