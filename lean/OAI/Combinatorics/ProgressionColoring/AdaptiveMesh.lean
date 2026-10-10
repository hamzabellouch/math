import OAI.Combinatorics.ProgressionColoring.CyclicModel
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum

namespace OAI

namespace QuantitativeVanDerWaerden

/-- Distance to the cut, expressed using the centered representative. -/
noncomputable def rho (x : ℝ) : ℝ := 1 / 2 - |centered x|

theorem rho_nonneg (x : ℝ) : 0 ≤ rho x := by
  have hx := centered_mem x
  have ha : |centered x| ≤ (1 / 2 : ℝ) := abs_le.mpr ⟨hx.1, hx.2.le⟩
  unfold rho
  linarith

theorem rho_le_half (x : ℝ) : rho x ≤ 1 / 2 := by
  unfold rho
  linarith [abs_nonneg (centered x)]

theorem rho_add_int (x : ℝ) (z : ℤ) : rho (x + z) = rho x := by
  simp only [rho, centered_add_int]

structure AdaptiveMesh where
  H : ℝ
  alpha : ℝ
  H_pos : 0 < H
  H_le : H ≤ 1 / 8
  alpha_pos : 0 < alpha
  alpha_le : alpha ≤ 1 / 4

namespace AdaptiveMesh

variable (A : AdaptiveMesh)

noncomputable def R : ℝ := Real.log (1 + 1 / (2 * A.alpha))
noncomputable def m : ℕ := ⌈A.R / A.H⌉₊
noncomputable def theta : ℝ := A.R / A.m
noncomputable def endpoint (j : ℕ) : ℝ :=
  A.alpha * (Real.exp ((j : ℝ) * A.theta) - 1)
noncomputable def radialWidth (j : ℕ) : ℝ := A.endpoint (j + 1) - A.endpoint j

theorem argument_ge_three : (3 : ℝ) ≤ 1 + 1 / (2 * A.alpha) := by
  have hp : 0 < 2 * A.alpha := by nlinarith [A.alpha_pos]
  have h : (2 : ℝ) ≤ 1 / (2 * A.alpha) :=
    (le_div_iff₀ hp).mpr (by nlinarith [A.alpha_le])
  linarith

theorem one_le_R : (1 : ℝ) ≤ A.R := by
  have hp : 0 < 1 + 1 / (2 * A.alpha) := by
    linarith [A.argument_ge_three]
  apply (Real.le_log_iff_exp_le hp).mpr
  have he : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  exact he.le.trans A.argument_ge_three

theorem R_pos : 0 < A.R := lt_of_lt_of_le (by norm_num) A.one_le_R

theorem m_pos : 0 < A.m := by
  exact Nat.ceil_pos.mpr (div_pos A.R_pos A.H_pos)

theorem m_cast_pos : (0 : ℝ) < A.m := by exact_mod_cast A.m_pos

theorem theta_pos : 0 < A.theta := div_pos A.R_pos A.m_cast_pos

theorem theta_le_H : A.theta ≤ A.H := by
  have hc : A.R / A.H ≤ (A.m : ℝ) := Nat.le_ceil _
  have hc' : A.R ≤ (A.m : ℝ) * A.H := (div_le_iff₀ A.H_pos).mp hc
  exact (div_le_iff₀ A.m_cast_pos).mpr (by simpa [mul_comm] using hc')

theorem half_H_le_theta : A.H / 2 ≤ A.theta := by
  have hHR : A.H ≤ A.R := by linarith [A.H_le, A.one_le_R]
  have hone : (1 : ℝ) ≤ A.R / A.H := (le_div_iff₀ A.H_pos).mpr (by simpa using hHR)
  have hc : (A.m : ℝ) < A.R / A.H + 1 :=
    Nat.ceil_lt_add_one (le_of_lt (div_pos A.R_pos A.H_pos))
  have hmul : (A.m : ℝ) * A.H ≤ 2 * A.R := by
    have hm : (A.m : ℝ) ≤ (2 * A.R) / A.H := by
      rw [mul_div_assoc]
      linarith
    exact (le_div_iff₀ A.H_pos).mp hm
  exact (le_div_iff₀ A.m_cast_pos).mpr (by nlinarith)

theorem theta_le_eighth : A.theta ≤ 1 / 8 := A.theta_le_H.trans A.H_le

theorem exp_theta_le_two : Real.exp A.theta ≤ 2 := by
  have ht : A.theta < 1 := by linarith [A.theta_le_eighth]
  have he := Real.exp_bound_div_one_sub_of_interval A.theta_pos.le ht
  have hm : Real.exp A.theta * (1 - A.theta) ≤ 1 :=
    (le_div_iff₀ (by linarith : 0 < 1 - A.theta)).mp he
  nlinarith [Real.exp_pos A.theta, A.theta_le_eighth]

theorem exp_theta_sub_one_le : Real.exp A.theta - 1 ≤ 2 * A.theta := by
  have ht : A.theta < 1 := by linarith [A.theta_le_eighth]
  have he := Real.exp_bound_div_one_sub_of_interval A.theta_pos.le ht
  have hm : Real.exp A.theta * (1 - A.theta) ≤ 1 :=
    (le_div_iff₀ (by linarith : 0 < 1 - A.theta)).mp he
  have hp := mul_nonneg A.theta_pos.le (sub_nonneg.mpr A.exp_theta_le_two)
  nlinarith

theorem theta_le_exp_theta_sub_one : A.theta ≤ Real.exp A.theta - 1 := by
  linarith [Real.add_one_le_exp A.theta]

@[simp] theorem endpoint_zero : A.endpoint 0 = 0 := by simp [endpoint]

theorem endpoint_strictMono : StrictMono A.endpoint := by
  intro i j hij
  unfold endpoint
  apply mul_lt_mul_of_pos_left _ A.alpha_pos
  apply sub_lt_sub_right
  apply Real.exp_lt_exp.mpr
  exact mul_lt_mul_of_pos_right (by exact_mod_cast hij) A.theta_pos

theorem endpoint_m : A.endpoint A.m = 1 / 2 := by
  have hm : (A.m : ℝ) ≠ 0 := ne_of_gt A.m_cast_pos
  have hmt : (A.m : ℝ) * A.theta = A.R := by
    dsimp [theta]
    field_simp [hm]
  have hp : 0 < 1 + 1 / (2 * A.alpha) := by
    linarith [A.argument_ge_three]
  rw [endpoint, hmt, R, Real.exp_log hp]
  have ha : A.alpha ≠ 0 := ne_of_gt A.alpha_pos
  field_simp [ha]
  ring

theorem radialWidth_pos (j : ℕ) : 0 < A.radialWidth j := by
  exact sub_pos.mpr (A.endpoint_strictMono (Nat.lt_succ_self j))

theorem radialWidth_eq (j : ℕ) :
    A.radialWidth j = A.alpha * Real.exp ((j : ℝ) * A.theta) *
      (Real.exp A.theta - 1) := by
  simp only [radialWidth, endpoint, Nat.cast_add, Nat.cast_one, add_mul,
    one_mul, Real.exp_add]
  ring

/-- The width estimate holds on the closed radial interval; this includes
the circle cut and zero once the two halves are realized as intervals. -/
theorem radial_width_bounds (j : ℕ) (r : ℝ)
    (hl : A.endpoint j ≤ r) (hu : r ≤ A.endpoint (j + 1)) :
    A.H / 4 * (r + A.alpha) ≤ A.radialWidth j ∧
      A.radialWidth j ≤ 2 * A.H * (r + A.alpha) := by
  let b := A.alpha * Real.exp ((j : ℝ) * A.theta)
  have hH : 0 < A.H := A.H_pos
  have hb : 0 < b := mul_pos A.alpha_pos (Real.exp_pos _)
  have hl' : b ≤ r + A.alpha := by dsimp [endpoint] at hl; dsimp [b]; nlinarith
  have hu' : r + A.alpha ≤ b * Real.exp A.theta := by
    simp only [endpoint, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
      Real.exp_add] at hu
    dsimp [b]
    nlinarith
  have hr : r + A.alpha ≤ 2 * b := by
    calc
      r + A.alpha ≤ b * Real.exp A.theta := hu'
      _ ≤ b * 2 := mul_le_mul_of_nonneg_left A.exp_theta_le_two hb.le
      _ = 2 * b := by ring
  rw [A.radialWidth_eq]
  change A.H / 4 * (r + A.alpha) ≤ b * (Real.exp A.theta - 1) ∧
    b * (Real.exp A.theta - 1) ≤ 2 * A.H * (r + A.alpha)
  constructor
  · calc
      A.H / 4 * (r + A.alpha) ≤ A.H / 4 * (2 * b) := by gcongr
      _ = b * (A.H / 2) := by ring
      _ ≤ b * A.theta := mul_le_mul_of_nonneg_left A.half_H_le_theta hb.le
      _ ≤ b * (Real.exp A.theta - 1) :=
        mul_le_mul_of_nonneg_left A.theta_le_exp_theta_sub_one hb.le
  · calc
      b * (Real.exp A.theta - 1) ≤ b * (2 * A.theta) :=
        mul_le_mul_of_nonneg_left A.exp_theta_sub_one_le hb.le
      _ ≤ b * (2 * A.H) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left A.theta_le_H (by norm_num)) hb.le
      _ ≤ (r + A.alpha) * (2 * A.H) :=
        mul_le_mul_of_nonneg_right hl' (by positivity)
      _ = 2 * A.H * (r + A.alpha) := by ring

/-- `false` denotes the negative half and `true` the positive half. -/
abbrev Label := Bool × Fin A.m

noncomputable def left (i : A.Label) : ℝ :=
  if i.1 then 1 / 2 - A.endpoint (i.2.val + 1) else -1 / 2 + A.endpoint i.2.val

noncomputable def right (i : A.Label) : ℝ :=
  if i.1 then 1 / 2 - A.endpoint i.2.val else -1 / 2 + A.endpoint (i.2.val + 1)

def Contains (i : A.Label) (x : ℝ) : Prop := A.left i ≤ x ∧ x < A.right i

noncomputable def width (i : A.Label) : ℝ := A.right i - A.left i

theorem width_eq_radialWidth (i : A.Label) : A.width i = A.radialWidth i.2.val := by
  rcases i with ⟨side, i⟩
  cases side <;> dsimp [width, left, right, radialWidth] <;> ring

theorem width_pos (i : A.Label) : 0 < A.width i := by
  rw [A.width_eq_radialWidth]
  exact A.radialWidth_pos _

end AdaptiveMesh
end QuantitativeVanDerWaerden

/- Actual half-open labels and their periodic geometry. -/

namespace QuantitativeVanDerWaerden

theorem centered_eq_of_mem {x : ℝ}
    (hl : -(1 / 2 : ℝ) ≤ x) (hu : x < 1 / 2) : centered x = x := by
  have hf : ⌊x + 1 / 2⌋ = (0 : ℤ) :=
    Int.floor_eq_zero_iff.mpr ⟨by linarith, by linarith⟩
  simp only [centered, hf, Int.cast_zero, sub_zero]

theorem rho_eq_of_closed_mem {x : ℝ}
    (hl : -(1 / 2 : ℝ) ≤ x) (hu : x ≤ 1 / 2) : rho x = 1 / 2 - |x| := by
  rcases hu.eq_or_lt with hx | hx
  · subst x
    norm_num [rho, centered]
  · rw [rho, centered_eq_of_mem hl hx]

private theorem abs_le_abs_add_int {x : ℝ}
    (hl : -(1 / 2 : ℝ) ≤ x) (hu : x ≤ 1 / 2) (z : ℤ) : |x| ≤ |x + z| := by
  have ha : |x| ≤ (1 / 2 : ℝ) := abs_le.mpr ⟨hl, hu⟩
  rcases lt_trichotomy z 0 with hz | hz | hz
  · have hz' : (z : ℝ) ≤ -1 := by exact_mod_cast (show z ≤ -1 by omega)
    rw [abs_of_nonpos (by linarith : x + (z : ℝ) ≤ 0)]
    linarith
  · subst z
    simp
  · have hz' : (1 : ℝ) ≤ z := by exact_mod_cast (show 1 ≤ z by omega)
    rw [abs_of_nonneg (by linarith : 0 ≤ x + (z : ℝ))]
    linarith

theorem centered_abs_minimal (x : ℝ) (z : ℤ) : |centered x| ≤ |x - z| := by
  have hc := centered_mem x
  have h := abs_le_abs_add_int hc.1 hc.2.le (⌊x + 1 / 2⌋ - z)
  convert h using 1
  congr 1
  simp only [centered, Int.cast_sub]
  ring

theorem centered_abs_sub_le (x y : ℝ) : |centered x| - |centered y| ≤ |x - y| := by
  have hm := centered_abs_minimal x ⌊y + 1 / 2⌋
  have he : x - (⌊y + 1 / 2⌋ : ℤ) = (x - y) + centered y := by
    dsimp [centered]
    ring
  rw [he] at hm
  have ht := abs_add_le (x - y) (centered y)
  linarith

theorem rho_lipschitz (x y : ℝ) : |rho x - rho y| ≤ |x - y| := by
  have hxy := centered_abs_sub_le x y
  have hyx := centered_abs_sub_le y x
  rw [abs_sub_comm y x] at hyx
  apply abs_le.mpr
  unfold rho
  constructor <;> linarith

theorem rho_lipschitz_integer (x y : ℝ) (z : ℤ) :
    |rho x - rho y| ≤ |x - y - z| := by
  have h := rho_lipschitz x (y + z)
  rw [rho_add_int] at h
  simpa only [sub_add_eq_sub_sub] using h

namespace AdaptiveMesh

variable (A : AdaptiveMesh)

private theorem increasing_cover_Ico (f : ℕ → ℝ) (_hf : StrictMono f)
    (n : ℕ) (r : ℝ) (hl : f 0 ≤ r) (hu : r < f n) :
    ∃ i : Fin n, f i.val ≤ r ∧ r < f (i.val + 1) := by
  classical
  have he : ∃ j : ℕ, r < f j := ⟨n, hu⟩
  let j := Nat.find he
  have hj : r < f j := Nat.find_spec he
  have hjn : j ≤ n := Nat.find_min' he hu
  have hj0 : 0 < j := by
    by_contra h
    have hz : j = 0 := by omega
    rw [hz] at hj
    linarith
  refine ⟨⟨j - 1, by omega⟩, ?_, ?_⟩
  · have hm : ¬ r < f (j - 1) := Nat.find_min he (by omega)
    exact le_of_not_gt hm
  · simpa only [show j - 1 + 1 = j by omega] using hj

private theorem increasing_cover_Ioc (f : ℕ → ℝ) (_hf : StrictMono f)
    (n : ℕ) (r : ℝ) (hl : f 0 < r) (hu : r ≤ f n) :
    ∃ i : Fin n, f i.val < r ∧ r ≤ f (i.val + 1) := by
  classical
  have he : ∃ j : ℕ, r ≤ f j := ⟨n, hu⟩
  let j := Nat.find he
  have hj : r ≤ f j := Nat.find_spec he
  have hjn : j ≤ n := Nat.find_min' he hu
  have hj0 : 0 < j := by
    by_contra h
    have hz : j = 0 := by omega
    rw [hz] at hj
    linarith
  refine ⟨⟨j - 1, by omega⟩, ?_, ?_⟩
  · have hm : ¬ r ≤ f (j - 1) := Nat.find_min he (by omega)
    exact lt_of_not_ge hm
  · simpa only [show j - 1 + 1 = j by omega] using hj

theorem endpoint_nonneg (j : ℕ) : 0 ≤ A.endpoint j := by
  have h := A.endpoint_strictMono.monotone (Nat.zero_le j)
  simpa using h

theorem endpoint_le_half {j : ℕ} (hj : j ≤ A.m) : A.endpoint j ≤ 1 / 2 := by
  have h := A.endpoint_strictMono.monotone hj
  simpa only [A.endpoint_m] using h

theorem left_ge_neg_half (i : A.Label) : -(1 / 2 : ℝ) ≤ A.left i := by
  rcases i with ⟨side, i⟩
  have h0 := A.endpoint_nonneg i.val
  have h1 := A.endpoint_le_half (show i.val + 1 ≤ A.m from i.isLt)
  cases side <;> dsimp [left] <;> linarith

theorem right_le_half (i : A.Label) : A.right i ≤ 1 / 2 := by
  rcases i with ⟨side, i⟩
  have h0 := A.endpoint_nonneg i.val
  have h1 := A.endpoint_le_half (show i.val + 1 ≤ A.m from i.isLt)
  cases side <;> dsimp [right] <;> linarith

theorem contains_iff_negative (i : Fin A.m) (x : ℝ) :
    A.Contains (false, i) x ↔
      A.endpoint i.val ≤ x + 1 / 2 ∧ x + 1 / 2 < A.endpoint (i.val + 1) := by
  dsimp [Contains, left, right]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem contains_iff_positive (i : Fin A.m) (x : ℝ) :
    A.Contains (true, i) x ↔
      A.endpoint i.val < 1 / 2 - x ∧ 1 / 2 - x ≤ A.endpoint (i.val + 1) := by
  dsimp [Contains, left, right]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem exists_label {x : ℝ} (hl : -(1 / 2 : ℝ) ≤ x) (hu : x < 1 / 2) :
    ∃ i : A.Label, A.Contains i x := by
  by_cases hx : x < 0
  · obtain ⟨i, hi⟩ := increasing_cover_Ico A.endpoint A.endpoint_strictMono A.m
      (x + 1 / 2) (by rw [A.endpoint_zero]; linarith)
      (by rw [A.endpoint_m]; linarith)
    exact ⟨(false, i), (A.contains_iff_negative i x).mpr hi⟩
  · obtain ⟨i, hi⟩ := increasing_cover_Ioc A.endpoint A.endpoint_strictMono A.m
      (1 / 2 - x) (by rw [A.endpoint_zero]; linarith)
      (by rw [A.endpoint_m]; linarith)
    exact ⟨(true, i), (A.contains_iff_positive i x).mpr hi⟩

private theorem increasing_Ico_unique (f : ℕ → ℝ) (hf : StrictMono f)
    {i j : ℕ} {x : ℝ} (hi : f i ≤ x ∧ x < f (i + 1))
    (hj : f j ≤ x ∧ x < f (j + 1)) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have hle := hf.monotone (show i + 1 ≤ j by omega)
    linarith [hi.2, hj.1]
  · exact h
  · have hle := hf.monotone (show j + 1 ≤ i by omega)
    linarith [hj.2, hi.1]

private theorem increasing_Ioc_unique (f : ℕ → ℝ) (hf : StrictMono f)
    {i j : ℕ} {x : ℝ} (hi : f i < x ∧ x ≤ f (i + 1))
    (hj : f j < x ∧ x ≤ f (j + 1)) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have hle := hf.monotone (show i + 1 ≤ j by omega)
    linarith [hi.2, hj.1]
  · exact h
  · have hle := hf.monotone (show j + 1 ≤ i by omega)
    linarith [hj.2, hi.1]

theorem contains_negative_lt_zero (i : Fin A.m) {x : ℝ}
    (hx : A.Contains (false, i) x) : x < 0 := by
  have h := (A.contains_iff_negative i x).mp hx
  have hb := A.endpoint_le_half (show i.val + 1 ≤ A.m from i.isLt)
  linarith [h.2]

theorem contains_positive_nonneg (i : Fin A.m) {x : ℝ}
    (hx : A.Contains (true, i) x) : 0 ≤ x := by
  have h := (A.contains_iff_positive i x).mp hx
  have hb := A.endpoint_le_half (show i.val + 1 ≤ A.m from i.isLt)
  linarith [h.2]

theorem label_unique (i j : A.Label) {x : ℝ}
    (hi : A.Contains i x) (hj : A.Contains j x) : i = j := by
  rcases i with ⟨side, i⟩
  rcases j with ⟨side', j⟩
  cases side <;> cases side'
  · have hij := increasing_Ico_unique A.endpoint A.endpoint_strictMono
      ((A.contains_iff_negative i x).mp hi) ((A.contains_iff_negative j x).mp hj)
    have hf : i = j := Fin.ext hij
    subst j
    rfl
  · linarith [A.contains_negative_lt_zero i hi, A.contains_positive_nonneg j hj]
  · linarith [A.contains_positive_nonneg i hi, A.contains_negative_lt_zero j hj]
  · have hij := increasing_Ioc_unique A.endpoint A.endpoint_strictMono
      ((A.contains_iff_positive i x).mp hi) ((A.contains_iff_positive j x).mp hj)
    have hf : i = j := Fin.ext hij
    subst j
    rfl

noncomputable def meshLabel (x : ℝ) : A.Label :=
  Classical.choose (A.exists_label (centered_mem x).1 (centered_mem x).2)

theorem meshLabel_contains (x : ℝ) : A.Contains (A.meshLabel x) (centered x) :=
  Classical.choose_spec (A.exists_label (centered_mem x).1 (centered_mem x).2)

theorem meshLabel_eq_iff (x : ℝ) (i : A.Label) :
    A.meshLabel x = i ↔ A.Contains i (centered x) := by
  constructor
  · intro h
    rw [← h]
    exact A.meshLabel_contains x
  · intro h
    exact A.label_unique _ _ (A.meshLabel_contains x) h

theorem meshLabel_add_int (x : ℝ) (z : ℤ) : A.meshLabel (x + z) = A.meshLabel x := by
  apply (A.meshLabel_eq_iff _ _).mpr
  rw [centered_add_int]
  exact A.meshLabel_contains x

theorem same_label_distance {x y : ℝ} (h : A.meshLabel x = A.meshLabel y) :
    |centered x - centered y| ≤ A.width (A.meshLabel x) := by
  have hx := A.meshLabel_contains x
  have hy := A.meshLabel_contains y
  rw [← h] at hy
  unfold Contains at hx hy
  unfold width
  apply abs_le.mpr
  constructor <;> linarith

theorem closed_radial_mem (i : A.Label) {x : ℝ}
    (hl : A.left i ≤ x) (hu : x ≤ A.right i) :
    A.endpoint i.2.val ≤ rho x ∧ rho x ≤ A.endpoint (i.2.val + 1) := by
  have hxmin : -(1 / 2 : ℝ) ≤ x := (A.left_ge_neg_half i).trans hl
  have hxmax : x ≤ 1 / 2 := hu.trans (A.right_le_half i)
  rw [rho_eq_of_closed_mem hxmin hxmax]
  rcases i with ⟨side, i⟩
  have hb := A.endpoint_le_half (show i.val + 1 ≤ A.m from i.isLt)
  cases side
  · dsimp [left, right] at hl hu
    have hx : x ≤ 0 := by linarith
    rw [abs_of_nonpos hx]
    constructor <;> linarith
  · dsimp [left, right] at hl hu
    have hx : 0 ≤ x := by linarith
    rw [abs_of_nonneg hx]
    constructor <;> linarith

theorem width_bounds_of_closed_mem (i : A.Label) {x : ℝ}
    (hl : A.left i ≤ x) (hu : x ≤ A.right i) :
    A.H / 4 * (rho x + A.alpha) ≤ A.width i ∧
      A.width i ≤ 2 * A.H * (rho x + A.alpha) := by
  have hx := A.closed_radial_mem i hl hu
  rw [A.width_eq_radialWidth]
  exact A.radial_width_bounds i.2.val (rho x) hx.1 hx.2

theorem width_le_two_H (i : A.Label) : A.width i ≤ 2 * A.H := by
  have hw := A.width_bounds_of_closed_mem i (le_refl _)
    (le_of_lt (sub_pos.mp (A.width_pos i)))
  have hr := rho_le_half (A.left i)
  have hH := A.H_pos
  have ha := A.alpha_le
  have hp := mul_nonneg (by positivity : 0 ≤ 2 * A.H)
    (by linarith : 0 ≤ 1 - (rho (A.left i) + A.alpha))
  nlinarith [hw.2]

/-- Integer congruence is kept explicit. A displacement of at most twice
the anchor width covers every point in its closed circle neighborhood. -/
theorem neighbor_width (i j : A.Label) {x y : ℝ}
    (hxl : A.left i ≤ x) (hxu : x ≤ A.right i)
    (hyl : A.left j ≤ y) (hyu : y ≤ A.right j)
    (hnear : ∃ z : ℤ, |y - x - z| ≤ 2 * A.width i) :
    A.width i / 16 ≤ A.width j := by
  obtain ⟨z, hz⟩ := hnear
  have hr := (rho_lipschitz_integer y x z).trans hz
  have hr' := (abs_le.mp hr).1
  have hi := A.width_bounds_of_closed_mem i hxl hxu
  have hj := A.width_bounds_of_closed_mem j hyl hyu
  have hH := A.H_pos
  have hHa := A.H_le
  have hrad : 0 ≤ rho x + A.alpha := by linarith [rho_nonneg x, A.alpha_pos]
  have hmult := mul_nonneg (by linarith : 0 ≤ 1 / 8 - A.H) hrad
  have hrhalf : (rho x + A.alpha) / 2 ≤ rho y + A.alpha := by
    nlinarith [hi.2]
  have hscaled := mul_le_mul_of_nonneg_left hrhalf (by positivity : 0 ≤ A.H / 4)
  nlinarith [hj.1, hi.2]

end AdaptiveMesh
end QuantitativeVanDerWaerden

namespace QuantitativeVanDerWaerden.AdaptiveMesh

variable (A : AdaptiveMesh)

@[simp] theorem card_label : Fintype.card A.Label = 2 * A.m := by
  simp [Label, Fintype.card_prod]

theorem twice_m_le : (2 : ℝ) * A.m ≤ 2 * (A.R / A.H) + 2 := by
  have h := Nat.ceil_lt_add_one (le_of_lt (div_pos A.R_pos A.H_pos))
  change (A.m : ℝ) < A.R / A.H + 1 at h
  linarith

theorem twice_m_le_of_H {k : ℕ} (_hk : 0 < k) (hH : A.H = 1 / (k : ℝ)^2) :
    (2 : ℝ) * A.m ≤ 2 * (k : ℝ)^2 * A.R + 2 := by
  have h := A.twice_m_le
  rw [hH] at h
  simpa only [div_div_eq_mul_div, div_one, mul_comm A.R ((k : ℝ)^2),
    ← mul_assoc] using h

end QuantitativeVanDerWaerden.AdaptiveMesh

end OAI
