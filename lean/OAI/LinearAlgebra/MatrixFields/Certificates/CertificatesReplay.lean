import Mathlib

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.Foundation.RationalLogCertificate

open scoped BigOperators

noncomputable def sumPower (t : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, t ^ (i + 1) / (i + 1)

def rationalSumPower (t : ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, t ^ (i + 1) / (i + 1)

noncomputable def realApprox (n : ℕ) (x : ℝ) : ℝ :=
  sumPower ((x - 1) / (x + 1)) n - sumPower (-((x - 1) / (x + 1))) n

def rationalApprox (n : ℕ) (x : ℚ) : ℚ :=
  rationalSumPower ((x - 1) / (x + 1)) n -
    rationalSumPower (-((x - 1) / (x + 1))) n

@[simp] theorem rationalSumPower_cast (t : ℚ) (n : ℕ) :
    (rationalSumPower t n : ℝ) = sumPower (t : ℝ) n := by
  simp [rationalSumPower, sumPower]

@[simp] theorem rationalApprox_cast (n : ℕ) (x : ℚ) :
    (rationalApprox n x : ℝ) = realApprox n (x : ℝ) := by
  simp [rationalApprox, realApprox]

theorem symmetric_expansion_error (t : ℝ) (ht : |t| < 1) (n : ℕ) :
    |(Real.log (1 + t) - Real.log (1 - t)) -
        (sumPower t n - sumPower (-t) n)| ≤
      2 * (|t| ^ (n + 1) / (1 - |t|)) := by
  have hminus : |sumPower t n + Real.log (1 - t)| ≤
      |t| ^ (n + 1) / (1 - |t|) :=
    Real.abs_log_sub_add_sum_range_le ht n
  have hplus : |sumPower (-t) n + Real.log (1 + t)| ≤
      |t| ^ (n + 1) / (1 - |t|) := by
    simpa only [sumPower, abs_neg, sub_neg_eq_add] using
      Real.abs_log_sub_add_sum_range_le (by simpa using ht : |-t| < 1) n
  calc
    _ = |(sumPower (-t) n + Real.log (1 + t)) -
        (sumPower t n + Real.log (1 - t))| := by congr 1; ring
    _ ≤ |sumPower (-t) n + Real.log (1 + t)| +
        |sumPower t n + Real.log (1 - t)| := abs_sub _ _
    _ ≤ 2 * (|t| ^ (n + 1) / (1 - |t|)) := by linarith

theorem normalized_variable_bounds (x : ℝ) (hlo : 1 ≤ x) (hhi : x ≤ 2) :
    0 ≤ (x - 1) / (x + 1) ∧ (x - 1) / (x + 1) ≤ 1 / 3 := by
  have hden : 0 < x + 1 := by linarith
  constructor
  · exact div_nonneg (sub_nonneg.mpr hlo) hden.le
  · apply (div_le_iff₀ hden).2
    linarith

theorem normalized_log_error (x : ℝ) (hlo : 1 ≤ x) (hhi : x ≤ 2) (n : ℕ) :
    |Real.log x - realApprox n x| ≤
      2 * (((x - 1) / (x + 1)) ^ (n + 1) / (1 - (x - 1) / (x + 1))) := by
  let t := (x - 1) / (x + 1)
  obtain ⟨ht0, ht3⟩ := normalized_variable_bounds x hlo hhi
  have ht1 : t < 1 := by dsimp [t]; linarith
  have hden : x + 1 ≠ 0 := by linarith
  have hminus : 1 - t ≠ 0 := by linarith
  have hplus : 1 + t ≠ 0 := by dsimp [t]; linarith
  have hratio : (1 + t) / (1 - t) = x := by
    dsimp [t]
    field_simp [hden]
    ring
  have hlog : Real.log x = Real.log (1 + t) - Real.log (1 - t) := by
    rw [← hratio]
    exact Real.log_div hplus hminus
  have ht0' : 0 ≤ t := ht0
  have herror := symmetric_expansion_error t (by rwa [abs_of_nonneg ht0']) n
  rw [abs_of_nonneg ht0'] at herror
  simpa only [realApprox, ← hlog, t] using herror

theorem normalized_log_error_80 (x : ℝ) (hlo : 1 ≤ x) (hhi : x ≤ 2) :
    |Real.log x - realApprox 80 x| < 1 / (2 : ℝ) ^ 120 := by
  obtain ⟨ht0, ht3⟩ := normalized_variable_bounds x hlo hhi
  apply lt_of_le_of_lt (normalized_log_error x hlo hhi 80)
  calc
    _ ≤ 2 * (((1 : ℝ) / 3) ^ 81 / (1 - 1 / 3)) := by gcongr
    _ < 1 / (2 : ℝ) ^ 120 := by norm_num

theorem rational_log_error_80 (x : ℚ) (hlo : 1 ≤ x) (hhi : x ≤ 2) :
    |Real.log (x : ℝ) - (rationalApprox 80 x : ℝ)| < 1 / (2 : ℝ) ^ 120 := by
  rw [rationalApprox_cast]
  exact normalized_log_error_80 (x : ℝ) (by exact_mod_cast hlo) (by exact_mod_cast hhi)

structure ReducedArgument (x : ℚ) where
  exponent : ℤ
  mantissa : ℚ
  lower : 1 ≤ mantissa
  upper : mantissa ≤ 2
  value : x = mantissa * (2 : ℚ) ^ exponent

def reducedApprox {x : ℚ} (d : ReducedArgument x) : ℚ :=
  rationalApprox 80 d.mantissa + (d.exponent : ℚ) * rationalApprox 80 2

theorem ReducedArgument.positive {x : ℚ} (d : ReducedArgument x) : 0 < x := by
  rw [d.value]
  exact mul_pos (lt_of_lt_of_le (by norm_num) d.lower) (zpow_pos (by norm_num) _)

theorem reduced_log_error {x : ℚ} (d : ReducedArgument x) :
    |Real.log (x : ℝ) - (reducedApprox d : ℝ)| ≤
      (1 + |(d.exponent : ℝ)|) / (2 : ℝ) ^ 120 := by
  have hm : (0 : ℝ) < d.mantissa := by
    have hlo : (1 : ℝ) ≤ d.mantissa := by exact_mod_cast d.lower
    linarith
  have hvalue : (x : ℝ) = (d.mantissa : ℝ) * (2 : ℝ) ^ d.exponent := by
    simpa only [Rat.cast_mul, Rat.cast_zpow, Rat.cast_ofNat] using
      congrArg (fun q : ℚ => (q : ℝ)) d.value
  have hlog : Real.log (x : ℝ) = Real.log (d.mantissa : ℝ) +
      (d.exponent : ℝ) * Real.log 2 := by
    rw [hvalue, Real.log_mul (ne_of_gt hm) (zpow_ne_zero _ (by norm_num)),
      Real.log_zpow]
  have hmerr := (rational_log_error_80 d.mantissa d.lower d.upper).le
  have htwoerr := (rational_log_error_80 2 (by norm_num) (by norm_num)).le
  have hcast : (reducedApprox d : ℝ) = (rationalApprox 80 d.mantissa : ℝ) +
      (d.exponent : ℝ) * (rationalApprox 80 2 : ℝ) := by
    simp [reducedApprox]
  rw [hlog, hcast]
  calc
    _ = |(Real.log (d.mantissa : ℝ) - (rationalApprox 80 d.mantissa : ℝ)) +
        (d.exponent : ℝ) * (Real.log 2 - (rationalApprox 80 2 : ℝ))| := by
      congr 1
      ring
    _ ≤ |Real.log (d.mantissa : ℝ) - (rationalApprox 80 d.mantissa : ℝ)| +
        |(d.exponent : ℝ)| * |Real.log 2 - (rationalApprox 80 2 : ℝ)| := by
      simpa only [abs_mul] using abs_add_le
        (Real.log (d.mantissa : ℝ) - (rationalApprox 80 d.mantissa : ℝ))
        ((d.exponent : ℝ) * (Real.log 2 - (rationalApprox 80 2 : ℝ)))
    _ ≤ 1 / (2 : ℝ) ^ 120 + |(d.exponent : ℝ)| * (1 / (2 : ℝ) ^ 120) := by
      exact add_le_add hmerr (mul_le_mul_of_nonneg_left htwoerr (abs_nonneg _))
    _ = (1 + |(d.exponent : ℝ)|) / (2 : ℝ) ^ 120 := by ring

theorem reduced_entropy_error {x : ℚ} (d : ReducedArgument x) :
    |(-(x : ℝ) * Real.log (x : ℝ)) - (-x * reducedApprox d : ℚ)| ≤
      (x : ℝ) * ((1 + |(d.exponent : ℝ)|) / (2 : ℝ) ^ 120) := by
  have hx : (0 : ℝ) ≤ x := by exact_mod_cast d.positive.le
  have hcast : ((-x * reducedApprox d : ℚ) : ℝ) = -(x : ℝ) * (reducedApprox d : ℝ) := by
    simp
  rw [hcast, ← mul_sub, abs_mul, abs_neg, abs_of_nonneg hx]
  exact mul_le_mul_of_nonneg_left (reduced_log_error d) hx

def finiteEntropyApprox {ι : Type*} [Fintype ι] (p : ι → ℚ)
    (d : ∀ i, ReducedArgument (p i)) : ℚ :=
  ∑ i, -p i * reducedApprox (d i)

theorem finite_entropy_error {ι : Type*} [Fintype ι] (p : ι → ℚ)
    (d : ∀ i, ReducedArgument (p i)) :
    |(∑ i, -(p i : ℝ) * Real.log (p i : ℝ)) - (finiteEntropyApprox p d : ℝ)| ≤
      ∑ i, (p i : ℝ) * ((1 + |((d i).exponent : ℝ)|) / (2 : ℝ) ^ 120) := by
  have hcast : (finiteEntropyApprox p d : ℝ) =
      ∑ i, ((-p i * reducedApprox (d i) : ℚ) : ℝ) := by
    simp [finiteEntropyApprox]
  rw [hcast, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |(-(p i : ℝ) * Real.log (p i : ℝ)) -
        ((-p i * reducedApprox (d i) : ℚ) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum (fun i _ => reduced_entropy_error (d i))

theorem finite_entropy_error_of_exponent_bound {ι : Type*} [Fintype ι]
    (p : ι → ℚ) (d : ∀ i, ReducedArgument (p i))
    (hnorm : ∑ i, p i = 1) (K : ℝ)
    (hK : ∀ i, |((d i).exponent : ℝ)| ≤ K) :
    |(∑ i, -(p i : ℝ) * Real.log (p i : ℝ)) - (finiteEntropyApprox p d : ℝ)| ≤
      (1 + K) / (2 : ℝ) ^ 120 := by
  apply (finite_entropy_error p d).trans
  have hnorm' : ∑ i, (p i : ℝ) = 1 := by exact_mod_cast hnorm
  calc
    _ ≤ ∑ i, (p i : ℝ) * ((1 + K) / (2 : ℝ) ^ 120) := by
      apply Finset.sum_le_sum
      intro i _
      have hp : (0 : ℝ) ≤ p i := by exact_mod_cast (d i).positive.le
      apply mul_le_mul_of_nonneg_left _ hp
      exact div_le_div_of_nonneg_right (add_le_add (le_refl 1) (hK i)) (by positivity)
    _ = (1 + K) / (2 : ℝ) ^ 120 := by rw [← Finset.sum_mul, hnorm', one_mul]

end MatrixMultiplication.Foundation.RationalLogCertificate

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.AllFieldCertificates

open MatrixMultiplication.Foundation.RationalLogCertificate

structure Ball where
  center : ℚ
  radius : ℚ
  deriving DecidableEq

namespace Ball

def Encloses (b : Ball) (x : ℝ) : Prop := |x - (b.center : ℝ)| ≤ (b.radius : ℝ)

def exact (q : ℚ) : Ball := ⟨q, 0⟩
def add (a b : Ball) : Ball := ⟨a.center + b.center, a.radius + b.radius⟩
def neg (a : Ball) : Ball := ⟨-a.center, a.radius⟩
def mul (a b : Ball) : Ball :=
  ⟨a.center * b.center,
    |a.center| * b.radius + |b.center| * a.radius + a.radius * b.radius⟩

def lower (b : Ball) : ℚ := b.center - b.radius
def upper (b : Ball) : ℚ := b.center + b.radius

def ofBounds (lo hi : ℚ) : Ball := ⟨(lo + hi) / 2, (hi - lo) / 2⟩

theorem nonnegative_radius {b : Ball} {x : ℝ} (h : b.Encloses x) : 0 ≤ b.radius := by
  have : (0 : ℝ) ≤ b.radius := (abs_nonneg _).trans h
  exact_mod_cast this

theorem bounds {b : Ball} {x : ℝ} (h : b.Encloses x) :
    (b.lower : ℝ) ≤ x ∧ x ≤ (b.upper : ℝ) := by
  obtain ⟨hl, hu⟩ := abs_le.mp h
  simp only [lower, upper, Rat.cast_sub, Rat.cast_add]
  constructor <;> linarith

theorem ofBounds_sound {lo hi : ℚ} {x : ℝ}
    (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ (hi : ℝ)) :
    (ofBounds lo hi).Encloses x := by
  simp only [Encloses, ofBounds, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_sub]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem exact_sound (q : ℚ) : (exact q).Encloses (q : ℝ) := by
  simp [Encloses, exact]

theorem add_sound {a b : Ball} {x y : ℝ} (hx : a.Encloses x) (hy : b.Encloses y) :
    (add a b).Encloses (x + y) := by
  unfold Encloses add
  simp only [Rat.cast_add]
  calc
    _ = |(x - (a.center : ℝ)) + (y - (b.center : ℝ))| := by congr 1; ring
    _ ≤ |x - (a.center : ℝ)| + |y - (b.center : ℝ)| := abs_add_le _ _
    _ ≤ _ := add_le_add hx hy

theorem neg_sound {a : Ball} {x : ℝ} (hx : a.Encloses x) :
    (neg a).Encloses (-x) := by
  simpa only [Encloses, neg, Rat.cast_neg, neg_sub_neg, abs_sub_comm] using hx

theorem mul_sound {a b : Ball} {x y : ℝ} (hx : a.Encloses x) (hy : b.Encloses y) :
    (mul a b).Encloses (x * y) := by
  have ha : (0 : ℝ) ≤ a.radius := by exact_mod_cast nonnegative_radius hx
  have hb : (0 : ℝ) ≤ b.radius := by exact_mod_cast nonnegative_radius hy
  unfold Encloses mul
  simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_abs]
  calc
    _ = |(a.center : ℝ) * (y - (b.center : ℝ)) +
          (b.center : ℝ) * (x - (a.center : ℝ)) +
          (x - (a.center : ℝ)) * (y - (b.center : ℝ))| := by congr 1; ring
    _ ≤ |(a.center : ℝ) * (y - (b.center : ℝ))| +
          |(b.center : ℝ) * (x - (a.center : ℝ))| +
          |(x - (a.center : ℝ)) * (y - (b.center : ℝ))| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
    _ = |(a.center : ℝ)| * |y - (b.center : ℝ)| +
          |(b.center : ℝ)| * |x - (a.center : ℝ)| +
          |x - (a.center : ℝ)| * |y - (b.center : ℝ)| := by simp only [abs_mul]
    _ ≤ _ := add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hy (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hx (abs_nonneg _)))
      (mul_le_mul hx hy (abs_nonneg _) ha)

theorem widen_sound {a b : Ball} {x : ℝ} (hx : a.Encloses x)
    (h : |a.center - b.center| + a.radius ≤ b.radius) : b.Encloses x := by
  have hc : |(a.center : ℝ) - (b.center : ℝ)| + (a.radius : ℝ) ≤ (b.radius : ℝ) := by
    exact_mod_cast h
  unfold Encloses
  calc
    _ = |(x - (a.center : ℝ)) + ((a.center : ℝ) - (b.center : ℝ))| := by congr 1; ring
    _ ≤ |x - (a.center : ℝ)| + |(a.center : ℝ) - (b.center : ℝ)| := abs_add_le _ _
    _ ≤ (a.radius : ℝ) + |(a.center : ℝ) - (b.center : ℝ)| := add_le_add hx (le_refl _)
    _ ≤ _ := by linarith

def inv (a : Ball) : Ball := ofBounds (1 / a.upper) (1 / a.lower)

theorem inv_sound {a : Ball} {x : ℝ} (hx : a.Encloses x)
    (hpos : 0 < a.lower) : (inv a).Encloses x⁻¹ := by
  have hlo : (0 : ℝ) < a.lower := by exact_mod_cast hpos
  obtain ⟨hl, hu⟩ := bounds hx
  have hxp : 0 < x := lt_of_lt_of_le hlo hl
  apply ofBounds_sound
  · simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_inv, one_div] using
      one_div_le_one_div_of_le hxp hu
  · simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_inv, one_div] using
      one_div_le_one_div_of_le hlo hl

end Ball

def reductionError {x : ℚ} (d : ReducedArgument x) : ℚ :=
  (1 + |(d.exponent : ℚ)|) / 2 ^ 120

theorem reduction_error_cast {x : ℚ} (d : ReducedArgument x) :
    (reductionError d : ℝ) = (1 + |(d.exponent : ℝ)|) / 2 ^ 120 := by
  simp [reductionError]

def logBall (b : Ball) (dl : ReducedArgument b.lower) (du : ReducedArgument b.upper) : Ball :=
  Ball.ofBounds (reducedApprox dl - reductionError dl) (reducedApprox du + reductionError du)

theorem logBall_sound {b : Ball} {x : ℝ} (hx : b.Encloses x)
    (dl : ReducedArgument b.lower) (du : ReducedArgument b.upper) :
    (logBall b dl du).Encloses (Real.log x) := by
  have hlo : (0 : ℝ) < b.lower := by exact_mod_cast dl.positive
  obtain ⟨hl, hu⟩ := Ball.bounds hx
  have hxp : 0 < x := lt_of_lt_of_le hlo hl
  have el := abs_le.mp (reduced_log_error dl)
  have eu := abs_le.mp (reduced_log_error du)
  apply Ball.ofBounds_sound
  · have hm := Real.log_le_log hlo hl
    simp only [Rat.cast_sub, reduction_error_cast]
    linarith [el.1]
  · have hm := Real.log_le_log hxp hu
    simp only [Rat.cast_add, reduction_error_cast]
    linarith [eu.2]

theorem log_center_lipschitz {b : Ball} {x : ℝ} (hx : b.Encloses x)
    (hpos : 0 < b.lower) :
    |Real.log x - Real.log (b.center : ℝ)| ≤ (b.radius / b.lower : ℚ) := by
  have hr : (0 : ℝ) ≤ b.radius := by exact_mod_cast Ball.nonnegative_radius hx
  have hl : (0 : ℝ) < b.lower := by exact_mod_cast hpos
  have hcl : (b.lower : ℝ) ≤ b.center := by
    simp only [Ball.lower, Rat.cast_sub]
    linarith
  have hc : (0 : ℝ) < b.center := hl.trans_le hcl
  obtain ⟨hxl, _⟩ := Ball.bounds hx
  have hxp : 0 < x := hl.trans_le hxl
  have logs (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
      Real.log a - Real.log c ≤ (a - c) / c := by
    rw [← Real.log_div ha.ne' hc.ne']
    have h := Real.log_le_sub_one_of_pos (div_pos ha hc)
    have he : a / c - 1 = (a - c) / c := by field_simp
    rwa [he] at h
  have hup : Real.log x - Real.log (b.center : ℝ) ≤ (b.radius : ℝ) / (b.lower : ℝ) := by
    calc
      _ ≤ (x - (b.center : ℝ)) / (b.center : ℝ) := logs _ _ hxp hc
      _ ≤ (b.radius : ℝ) / (b.center : ℝ) :=
        div_le_div_of_nonneg_right (abs_le.mp hx).2 hc.le
      _ ≤ _ := div_le_div_of_nonneg_left hr hl hcl
  have hdown : Real.log (b.center : ℝ) - Real.log x ≤
      (b.radius : ℝ) / (b.lower : ℝ) := by
    calc
      _ ≤ ((b.center : ℝ) - x) / x := logs _ _ hc hxp
      _ ≤ (b.radius : ℝ) / x :=
        div_le_div_of_nonneg_right (by linarith [(abs_le.mp hx).1]) hxp.le
      _ ≤ _ := div_le_div_of_nonneg_left hr hl hxl
  rw [Rat.cast_div]
  exact abs_le.mpr ⟨by linarith, hup⟩

inductive Expression where
  | constant : ℚ → Expression
  | add : Expression → Expression → Expression
  | neg : Expression → Expression
  | mul : Expression → Expression → Expression
  | inv : Expression → Expression
  | log : Expression → Expression

noncomputable def Expression.value : Expression → ℝ
  | .constant q => q
  | .add a b => a.value + b.value
  | .neg a => -a.value
  | .mul a b => a.value * b.value
  | .inv a => a.value⁻¹
  | .log a => Real.log a.value

inductive Certificate : Expression → Ball → Prop where
  | constant (q : ℚ) : Certificate (.constant q) (.exact q)
  | add {e f a b} : Certificate e a → Certificate f b → Certificate (.add e f) (.add a b)
  | neg {e a} : Certificate e a → Certificate (.neg e) (.neg a)
  | mul {e f a b} : Certificate e a → Certificate f b → Certificate (.mul e f) (.mul a b)
  | inv {e a} : Certificate e a → 0 < a.lower → Certificate (.inv e) (.inv a)
  | log {e a} (dl : ReducedArgument a.lower) (du : ReducedArgument a.upper) :
      Certificate e a → Certificate (.log e) (logBall a dl du)
  | widen {e a b} : Certificate e a → |a.center - b.center| + a.radius ≤ b.radius →
      Certificate e b

theorem Certificate.sound {e : Expression} {b : Ball} (h : Certificate e b) :
    b.Encloses e.value := by
  induction h with
  | constant q => exact Ball.exact_sound q
  | add _ _ ih₁ ih₂ => exact Ball.add_sound ih₁ ih₂
  | neg _ ih => exact Ball.neg_sound ih
  | mul _ _ ih₁ ih₂ => exact Ball.mul_sound ih₁ ih₂
  | inv _ hp ih => exact Ball.inv_sound ih hp
  | log dl du _ ih => exact logBall_sound ih dl du
  | widen _ hw ih => exact Ball.widen_sound ih hw

theorem published_endpoint_below_target :
    (2371054886006745685 : ℚ) / 10 ^ 18 < (2371054887 : ℚ) / 10 ^ 9 := by
  decide +kernel

theorem value_below_target_of_certificate {e : Expression} {b : Ball}
    (hc : Certificate e b)
    (hu : b.upper ≤ (2371054886006745685 : ℚ) / 10 ^ 18) :
    e.value < (2371054887 : ℝ) / 10 ^ 9 := by
  have hbound := (Ball.bounds hc.sound).2
  have hu' : (b.upper : ℝ) ≤ (2371054886006745685 : ℝ) / 10 ^ 18 := by
    have hcast : (b.upper : ℝ) ≤ ((2371054886006745685 / 10 ^ 18 : ℚ) : ℝ) :=
      Rat.cast_le.mpr hu
    simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using hcast
  have htarget : (2371054886006745685 : ℝ) / 10 ^ 18 <
      (2371054887 : ℝ) / 10 ^ 9 := by
    have hcast : ((2371054886006745685 / 10 ^ 18 : ℚ) : ℝ) <
        ((2371054887 / 10 ^ 9 : ℚ) : ℝ) := Rat.cast_lt.mpr published_endpoint_below_target
    simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using hcast
  exact lt_of_le_of_lt (hbound.trans hu') htarget

end MatrixMultiplication.AllFieldCertificates

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.AllFieldCertificates.Replay

open MatrixMultiplication.Foundation.RationalLogCertificate

inductive Op where
  | constant (q : ℚ)
  | add (i j : ℕ)
  | neg (i : ℕ)
  | mul (i j : ℕ)
  | inv (i : ℕ)
  | log (i : ℕ)
  deriving DecidableEq, Repr

instance : Hashable Op where
  hash
    | .constant q => hash ((0 : ℕ), q.num, q.den)
    | .add i j => hash ((1 : ℕ), i, j)
    | .neg i => hash ((2 : ℕ), i)
    | .mul i j => hash ((3 : ℕ), i, j)
    | .inv i => hash ((4 : ℕ), i)
    | .log i => hash ((5 : ℕ), i)

abbrev Program := Array Op

noncomputable def Op.value (v : ℕ → ℝ) : Op → ℝ
  | .constant q => q
  | .add i j => v i + v j
  | .neg i => -v i
  | .mul i j => v i * v j
  | .inv i => (v i)⁻¹
  | .log i => Real.log (v i)

noncomputable def Program.eval (p : Program) : Array ℝ :=
  p.foldl (fun v op => v.push (op.value (fun i => v[i]?.getD 0))) #[]

def contains (a b : Ball) : Bool :=
  decide (|a.center - b.center| + a.radius ≤ b.radius)

theorem contains_sound {a b : Ball} {x : ℝ}
    (ha : a.Encloses x) (hab : contains a b = true) : b.Encloses x :=
  Ball.widen_sound ha (of_decide_eq_true hab)

noncomputable def polynomial (t : ℝ) : List ℚ → ℝ
  | [] => 0
  | a :: as => (a : ℝ) + t * polynomial t as

def traceHead (trace : List Ball) : Ball := trace.headD (.exact 0)

def checkPolynomial (t : Ball) : List ℚ → List Ball → Bool
  | [], [] => true
  | a :: as, b :: bs =>
      contains (Ball.add (.exact a) (Ball.mul t (traceHead bs))) b &&
        checkPolynomial t as bs
  | _, _ => false

theorem checkPolynomial_sound {t : Ball} {x : ℝ} (hx : t.Encloses x)
    (as : List ℚ) (trace : List Ball)
    (h : checkPolynomial t as trace = true) :
    (traceHead trace).Encloses (polynomial x as) := by
  induction as generalizing trace with
  | nil =>
      cases trace with
      | nil => simpa [traceHead, polynomial] using Ball.exact_sound 0
      | cons b bs => simp [checkPolynomial] at h
  | cons a as ih =>
      cases trace with
      | nil => simp [checkPolynomial] at h
      | cons b bs =>
          simp only [checkPolynomial, Bool.and_eq_true] at h
          exact contains_sound
            (Ball.add_sound (Ball.exact_sound a) (Ball.mul_sound hx (ih bs h.2))) h.1

def logCoefficients : List ℚ :=
  (List.range 24).map (fun i => 1 / (2 * (i : ℚ) + 1))

theorem realApprox_eq_polynomial (x : ℝ) :
    realApprox 48 x =
      2 * ((x - 1) / (x + 1)) *
        polynomial (((x - 1) / (x + 1)) ^ 2) logCoefficients := by
  simp only [realApprox, sumPower]
  norm_num [Finset.sum_range_succ, logCoefficients, List.range_succ,
    polynomial, List.map_append, List.foldr_append]
  ring

theorem normalized_log_error_48 (x : ℝ) (hlo : 1 ≤ x) (hhi : x ≤ 2) :
    |Real.log x - realApprox 48 x| < 1 / (2 : ℝ) ^ 72 := by
  obtain ⟨ht0, ht3⟩ := normalized_variable_bounds x hlo hhi
  apply lt_of_le_of_lt (normalized_log_error x hlo hhi 48)
  calc
    _ ≤ 2 * (((1 : ℝ) / 3) ^ 49 / (1 - 1 / 3)) := by gcongr
    _ < 1 / (2 : ℝ) ^ 72 := by norm_num

def pad (b : Ball) (error : ℚ) : Ball := ⟨b.center, b.radius + error⟩

theorem pad_sound {b : Ball} {x y : ℝ} {error : ℚ}
    (hx : b.Encloses x) (hxy : |y - x| ≤ (error : ℝ)) :
    (pad b error).Encloses y := by
  unfold Ball.Encloses pad at *
  simp only [Rat.cast_add]
  calc
    _ = |(y - x) + (x - (b.center : ℝ))| := by congr 1; ring
    _ ≤ |y - x| + |x - (b.center : ℝ)| := abs_add_le _ _
    _ ≤ (error : ℝ) + (b.radius : ℝ) := add_le_add hxy hx
    _ = _ := by ring

def logVariable (m : ℚ) : ℚ := (m - 1) / (m + 1)

def normalizedLogBall (m : ℚ) (trace : List Ball) : Ball :=
  pad (Ball.mul (.exact (2 * logVariable m)) (traceHead trace)) (1 / 2 ^ 72)

theorem normalizedLogBall_sound {m : ℚ} {trace : List Ball}
    (hlo : 1 ≤ m) (hhi : m ≤ 2)
    (hc : checkPolynomial (.exact (logVariable m ^ 2)) logCoefficients trace = true) :
    (normalizedLogBall m trace).Encloses (Real.log (m : ℝ)) := by
  have hp := checkPolynomial_sound (Ball.exact_sound (logVariable m ^ 2))
    logCoefficients trace hc
  have hv : (logVariable m : ℝ) = ((m : ℝ) - 1) / ((m : ℝ) + 1) := by
    simp [logVariable]
  have ha : (Ball.mul (.exact (2 * logVariable m)) (traceHead trace)).Encloses
      (realApprox 48 (m : ℝ)) := by
    rw [realApprox_eq_polynomial]
    convert Ball.mul_sound (Ball.exact_sound (2 * logVariable m)) hp using 1
    simp [hv]
  apply pad_sound ha
  have h := (normalized_log_error_48 (m : ℝ)
    (by exact_mod_cast hlo) (by exact_mod_cast hhi)).le
  simpa using h

end MatrixMultiplication.AllFieldCertificates.Replay

namespace MatrixMultiplication.CompactCertificate

structure NInterval where
  lo : ℕ
  hi : ℕ
  deriving DecidableEq, Repr

namespace NInterval

def Encloses (S : ℕ) (a : NInterval) (x : ℝ) : Prop :=
  (a.lo : ℝ) / S ≤ x ∧ x ≤ (a.hi : ℝ) / S

def zero : NInterval := ⟨0, 0⟩
def add (a b : NInterval) : NInterval := ⟨a.lo + b.lo, a.hi + b.hi⟩
def mul (S : ℕ) (a b : NInterval) : NInterval :=
  ⟨a.lo * b.lo / S, a.hi * b.hi / S + 1⟩
def frac (S n d : ℕ) : NInterval := ⟨n * S / d, n * S / d + 1⟩

lemma div_floor_bounds (n d : ℕ) (hd : 0 < d) :
    ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d ∧
    (n : ℝ) / d ≤ ((n / d : ℕ) : ℝ) + 1 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · apply (le_div_iff₀ hd').2
    exact_mod_cast Nat.div_mul_le_self n d
  · apply (div_le_iff₀ hd').2
    have h := Nat.lt_div_mul_add (a := n) hd
    exact_mod_cast (by simpa only [Nat.add_mul, Nat.one_mul] using h.le : n ≤ (n / d + 1) * d)

lemma zero_sound (S : ℕ) : Encloses S zero 0 := by simp [Encloses, zero]

lemma nonneg {S : ℕ} {a : NInterval} {x : ℝ} (h : Encloses S a x) : 0 ≤ x :=
  (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans h.1

lemma add_sound {S : ℕ} {a b : NInterval} {x y : ℝ}
    (hx : Encloses S a x) (hy : Encloses S b y) :
    Encloses S (add a b) (x + y) := by
  simpa [Encloses, add, Nat.cast_add, add_div] using And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

lemma mul_sound {S : ℕ} (hS : 0 < S) {a b : NInterval} {x y : ℝ}
    (hx : Encloses S a x) (hy : Encloses S b y) :
    Encloses S (mul S a b) (x * y) := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hlo := (div_floor_bounds (a.lo * b.lo) S hS).1
  have hhi := (div_floor_bounds (a.hi * b.hi) S hS).2
  unfold Encloses mul
  simp only [Nat.cast_add, Nat.cast_one]
  constructor
  · calc
      _ ≤ ((a.lo : ℝ) * b.lo / S) / S := by
        exact div_le_div_of_nonneg_right (by simpa only [Nat.cast_mul] using hlo) hS'.le
      _ = ((a.lo : ℝ) / S) * ((b.lo : ℝ) / S) := by ring
      _ ≤ x * y := mul_le_mul hx.1 hy.1 (by positivity) (nonneg hx)
  · calc
      x * y ≤ ((a.hi : ℝ) / S) * ((b.hi : ℝ) / S) :=
        mul_le_mul hx.2 hy.2 (nonneg hy) (by positivity)
      _ = ((a.hi : ℝ) * b.hi / S) / S := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by simpa only [Nat.cast_mul] using hhi) hS'.le

lemma frac_sound {S n d : ℕ} (hS : 0 < S) (hd : 0 < d) :
    Encloses S (frac S n d) ((n : ℝ) / d) := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hb := div_floor_bounds (n * S) d hd
  unfold Encloses frac
  simp only [Nat.cast_add, Nat.cast_one]
  constructor
  · calc
      _ ≤ ((n : ℝ) * S / d) / S :=
        div_le_div_of_nonneg_right (by simpa only [Nat.cast_mul] using hb.1) hS'.le
      _ = _ := by field_simp
  · calc
      (n : ℝ) / d = ((n : ℝ) * S / d) / S := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (by simpa only [Nat.cast_mul] using hb.2) hS'.le

def oddHorner (S : ℕ) (t : NInterval) (start : ℕ) : ℕ → NInterval
  | 0 => zero
  | n + 1 => add (frac S 1 (2 * start + 1))
      (mul S t (oddHorner S t (start + 1) n))

noncomputable def oddPolynomial (t : ℝ) (start : ℕ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => 1 / (2 * (start : ℝ) + 1) + t * oddPolynomial t (start + 1) n

lemma oddHorner_sound {S : ℕ} (hS : 0 < S) {t : NInterval} {x : ℝ}
    (hx : Encloses S t x) (start n : ℕ) :
    Encloses S (oddHorner S t start n) (oddPolynomial x start n) := by
  induction n generalizing start with
  | zero => exact zero_sound S
  | succ n ih =>
    apply add_sound
    · simpa only [Nat.cast_one, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
        using (frac_sound (n := 1) hS (by omega : 0 < 2 * start + 1))
    · exact mul_sound hS hx (ih (start + 1))

end NInterval
end MatrixMultiplication.CompactCertificate

namespace MatrixMultiplication.CompactCertificate
open AllFieldCertificates AllFieldCertificates.Replay
open Foundation.RationalLogCertificate

lemma oddPolynomial_eq (x : ℝ) :
    NInterval.oddPolynomial x 0 24 = polynomial x logCoefficients := by
  norm_num [NInterval.oddPolynomial, polynomial, logCoefficients, List.range_succ]

def scale : ℕ := 10 ^ 40
lemma scale_pos : 0 < scale := by decide

def logApprox (n d : ℕ) : NInterval :=
  let u := NInterval.frac scale (n - d) (n + d)
  NInterval.mul scale (NInterval.add u u)
    (NInterval.oddHorner scale (NInterval.mul scale u u) 0 24)

lemma logApprox_sound {n d : ℕ} (hd : 0 < d) (hlo : d ≤ n) :
    (logApprox n d).Encloses scale (realApprox 48 ((n : ℝ) / d)) := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hsum : 0 < n + d := by omega
  have hu := NInterval.frac_sound (n := n - d) scale_pos hsum
  have heq : (((n : ℝ) / d - 1) / ((n : ℝ) / d + 1)) =
      ((n - d : ℕ) : ℝ) / (n + d : ℕ) := by
    rw [Nat.cast_sub hlo, Nat.cast_add]
    field_simp
  rw [realApprox_eq_polynomial, heq, ← oddPolynomial_eq]
  simpa only [logApprox, two_mul, pow_two] using
    NInterval.mul_sound scale_pos (NInterval.add_sound hu hu)
      (NInterval.oddHorner_sound scale_pos (NInterval.mul_sound scale_pos hu hu) 0 24)

def NInterval.ball (a : NInterval) : Ball :=
  Ball.ofBounds ((a.lo : ℚ) / scale) ((a.hi : ℚ) / scale)

lemma NInterval.ball_sound {a : NInterval} {x : ℝ} (h : a.Encloses scale x) :
    a.ball.Encloses x := by
  apply Ball.ofBounds_sound
  · simpa only [Rat.cast_div, Rat.cast_natCast] using h.1
  · simpa only [Rat.cast_div, Rat.cast_natCast] using h.2

def normalized (n d : ℕ) : Ball := pad (logApprox n d).ball (1 / 2 ^ 72)

lemma normalized_sound {n d : ℕ} (hd : 0 < d) (hlo : d ≤ n) (hhi : n ≤ 2 * d) :
    (normalized n d).Encloses (Real.log ((n : ℝ) / d)) := by
  apply pad_sound (NInterval.ball_sound (logApprox_sound hd hlo))
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hl : 1 ≤ (n : ℝ) / d := (le_div_iff₀ hd').2 (by simpa only [one_mul] using (Nat.cast_le.mpr hlo : (d : ℝ) ≤ n))
  have hh : (n : ℝ) / d ≤ 2 := (div_le_iff₀ hd').2 (by exact_mod_cast hhi)
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using
    (normalized_log_error_48 ((n : ℝ) / d) hl hh).le

structure LogData where
  exponent : ℤ
  numerator : ℕ
  denominator : ℕ
  deriving DecidableEq

def logResult (two a : Ball) (w : LogData) : Ball :=
  pad (Ball.add (normalized w.numerator w.denominator)
    (Ball.mul (.exact w.exponent) two)) (a.radius / a.lower)

def checkLog (two a b : Ball) (w : LogData) : Bool :=
  decide (0 < a.lower ∧ 0 < w.denominator ∧ w.denominator ≤ w.numerator ∧
    w.numerator ≤ 2 * w.denominator ∧
    a.center = (w.numerator : ℚ) / w.denominator * (2 : ℚ) ^ w.exponent) &&
  contains (logResult two a w) b

lemma checkLog_sound {two a b : Ball} {w : LogData} {x : ℝ}
    (htwo : two.Encloses (Real.log 2)) (hx : a.Encloses x)
    (h : checkLog two a b w = true) : b.Encloses (Real.log x) := by
  simp only [checkLog, Bool.and_eq_true] at h
  obtain ⟨hpos, hd, hlo, hhi, heq⟩ := of_decide_eq_true h.1
  have hm : (0 : ℝ) < (w.numerator : ℝ) / w.denominator := by
    have hn : 0 < w.numerator := lt_of_lt_of_le hd hlo
    exact div_pos (Nat.cast_pos.mpr hn) (Nat.cast_pos.mpr hd)
  have heq' : (a.center : ℝ) = ((w.numerator : ℝ) / w.denominator) * (2 : ℝ) ^ w.exponent := by
    simpa only [Rat.cast_mul, Rat.cast_zpow, Rat.cast_ofNat, Rat.cast_div, Rat.cast_natCast] using
      congrArg (fun q : ℚ => (q : ℝ)) heq
  have hlog : Real.log (a.center : ℝ) =
      Real.log ((w.numerator : ℝ) / w.denominator) + (w.exponent : ℝ) * Real.log 2 := by
    rw [heq', Real.log_mul (ne_of_gt hm) (zpow_ne_zero _ (by norm_num)), Real.log_zpow]
  have hcenter : (Ball.add (normalized w.numerator w.denominator)
      (Ball.mul (.exact w.exponent) two)).Encloses (Real.log (a.center : ℝ)) := by
    rw [hlog]
    exact Ball.add_sound (normalized_sound hd hlo hhi)
      (by simpa using Ball.mul_sound (Ball.exact_sound (w.exponent : ℚ)) htwo)
  exact contains_sound (pad_sound hcenter (log_center_lipschitz hx hpos)) h.2

end MatrixMultiplication.CompactCertificate

namespace MatrixMultiplication.AllFieldCertificates.Replay
abbrev LogWitness := MatrixMultiplication.CompactCertificate.LogData
abbrev logResult := MatrixMultiplication.CompactCertificate.logResult

def checkLog (two a b : Ball) (w : LogWitness) : Bool :=
  decide (0 < a.lower ∧ 0 < w.denominator ∧ w.denominator ≤ w.numerator ∧
    w.numerator ≤ 2 * w.denominator ∧
    a.center = (w.numerator : ℚ) / w.denominator * (2 : ℚ) ^ w.exponent) &&
  contains (logResult two a w) b

theorem checkLog_sound {two a b : Ball} {w : LogWitness} {x : ℝ}
    (htwo : two.Encloses (Real.log 2)) (hx : a.Encloses x)
    (h : checkLog two a b w = true) : b.Encloses (Real.log x) :=
  MatrixMultiplication.CompactCertificate.checkLog_sound htwo hx h

structure Witness where
  ball : Ball
  logarithm : Option LogWitness := none
  deriving DecidableEq

def ballAt (v : Array Ball) (i : ℕ) : Ball := v[i]?.getD (.exact 0)

def checkStep (two : Ball) (v : Array Ball) (op : Op) (w : Witness) : Bool :=
  match op with
  | .constant q => contains (.exact q) w.ball
  | .add i j => contains (Ball.add (ballAt v i) (ballAt v j)) w.ball
  | .neg i => contains (Ball.neg (ballAt v i)) w.ball
  | .mul i j => contains (Ball.mul (ballAt v i) (ballAt v j)) w.ball
  | .inv i => decide (0 < (ballAt v i).lower) && contains (Ball.inv (ballAt v i)) w.ball
  | .log i => match w.logarithm with
    | none => false
    | some lw => checkLog two (ballAt v i) w.ball lw

def Related (bs : Array Ball) (vs : Array ℝ) : Prop :=
  bs.size = vs.size ∧ ∀ i, (ballAt bs i).Encloses (vs[i]?.getD 0)

theorem checkStep_sound {two : Ball} (htwo : two.Encloses (Real.log 2))
    {bs : Array Ball} {vs : Array ℝ} (hr : Related bs vs)
    {op : Op} {w : Witness} (hc : checkStep two bs op w = true) :
    w.ball.Encloses (op.value (fun i => vs[i]?.getD 0)) := by
  cases op with
  | constant q => exact contains_sound (Ball.exact_sound q) hc
  | add i j => exact contains_sound (Ball.add_sound (hr.2 i) (hr.2 j)) hc
  | neg i => exact contains_sound (Ball.neg_sound (hr.2 i)) hc
  | mul i j => exact contains_sound (Ball.mul_sound (hr.2 i) (hr.2 j)) hc
  | inv i =>
      simp only [checkStep, Bool.and_eq_true] at hc
      exact contains_sound (Ball.inv_sound (hr.2 i) (of_decide_eq_true hc.1)) hc.2
  | log i =>
      cases hw : w.logarithm with
      | none => simp [checkStep, hw] at hc
      | some lw =>
          simp only [checkStep, hw] at hc
          exact checkLog_sound htwo (hr.2 i) hc

theorem Related.push {bs : Array Ball} {vs : Array ℝ} (hr : Related bs vs)
    {b : Ball} {v : ℝ} (hv : b.Encloses v) : Related (bs.push b) (vs.push v) := by
  constructor
  · simpa using hr.1
  · intro i
    simp only [ballAt, Array.getElem?_push, ← hr.1]
    split_ifs with hi
    · exact hv
    · exact hr.2 i

theorem Related.empty : Related #[] #[] := by
  constructor
  · rfl
  · intro i
    simpa [ballAt] using Ball.exact_sound 0

noncomputable def evalFrom (ops : List Op) (vs : Array ℝ) : Array ℝ :=
  ops.foldl (fun v op => v.push (op.value (fun i => v[i]?.getD 0))) vs

def ballsFrom (ws : List Witness) (bs : Array Ball) : Array Ball :=
  ws.foldl (fun b w => b.push w.ball) bs

def checkFrom (two : Ball) : List Op → List Witness → Array Ball → Bool
  | [], [], _ => true
  | op :: ops, w :: ws, bs =>
      checkStep two bs op w && checkFrom two ops ws (bs.push w.ball)
  | _, _, _ => false

theorem checkFrom_sound {two : Ball} (htwo : two.Encloses (Real.log 2))
    (ops : List Op) (ws : List Witness) {bs : Array Ball} {vs : Array ℝ}
    (hr : Related bs vs) (hc : checkFrom two ops ws bs = true) :
    Related (ballsFrom ws bs) (evalFrom ops vs) := by
  induction ops generalizing ws bs vs with
  | nil =>
      cases ws with
      | nil => exact hr
      | cons w ws => simp [checkFrom] at hc
  | cons op ops ih =>
      cases ws with
      | nil => simp [checkFrom] at hc
      | cons w ws =>
          simp only [checkFrom, Bool.and_eq_true] at hc
          exact ih ws (hr.push (checkStep_sound htwo hr hc.1)) hc.2

def checkProgram (two : Ball) (p : Program) (ws : List Witness) : Bool :=
  checkFrom two p.toList ws #[]

theorem checkProgram_sound {two : Ball} (htwo : two.Encloses (Real.log 2))
    {p : Program} {ws : List Witness} (hc : checkProgram two p ws = true) :
    Related (ballsFrom ws #[]) p.eval := by
  have h := checkFrom_sound htwo p.toList ws Related.empty hc
  simpa only [evalFrom, Array.foldl_toList, Program.eval] using h

theorem evalFrom_append (as bs : List Op) (v : Array ℝ) :
    evalFrom (as ++ bs) v = evalFrom bs (evalFrom as v) := by
  simp [evalFrom, List.foldl_append]

theorem ballsFrom_append (as bs : List Witness) (v : Array Ball) :
    ballsFrom (as ++ bs) v = ballsFrom bs (ballsFrom as v) := by
  simp [ballsFrom, List.foldl_append]

theorem checkFrom_append (two : Ball) (as bs : List Op) (aw bw : List Witness)
    (v : Array Ball) (hlen : as.length = aw.length) :
    checkFrom two (as ++ bs) (aw ++ bw) v =
      (checkFrom two as aw v && checkFrom two bs bw (ballsFrom aw v)) := by
  induction as generalizing aw v with
  | nil =>
      cases aw with
      | nil => simp [checkFrom, ballsFrom]
      | cons w ws => simp at hlen
  | cons a as ih =>
      cases aw with
      | nil => simp at hlen
      | cons w ws =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
          simp only [List.cons_append, checkFrom, ballsFrom, List.foldl_cons]
          rw [ih ws (v.push w.ball) hlen]
          exact (Bool.and_assoc _ _ _).symm

theorem checked_upper_bound {two : Ball} (htwo : two.Encloses (Real.log 2))
    {p : Program} {ws : List Witness} (hc : checkProgram two p ws = true)
    (i : ℕ) (bound : ℚ) (hb : (ballAt (ballsFrom ws #[]) i).upper ≤ bound) :
    p.eval[i]?.getD 0 ≤ (bound : ℝ) := by
  have hv := (Ball.bounds ((checkProgram_sound htwo hc).2 i)).2
  exact hv.trans (by exact_mod_cast hb)

theorem checked_below_target {two : Ball} (htwo : two.Encloses (Real.log 2))
    {p : Program} {ws : List Witness} (hc : checkProgram two p ws = true)
    (i : ℕ) (hb : (ballAt (ballsFrom ws #[]) i).upper < (2371054887 : ℚ) / 10 ^ 9) :
    p.eval[i]?.getD 0 < (2371054887 : ℝ) / 10 ^ 9 := by
  have hv := (Ball.bounds ((checkProgram_sound htwo hc).2 i)).2
  apply lt_of_le_of_lt hv
  have hcast : ((ballAt (ballsFrom ws #[]) i).upper : ℝ) <
      (((2371054887 : ℚ) / 10 ^ 9 : ℚ) : ℝ) := Rat.cast_lt.mpr hb
  simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using hcast

end MatrixMultiplication.AllFieldCertificates.Replay

end

end MatrixAllFields

end OAI
