import OAI.LinearAlgebra.MatrixMultiplication.Numerical.ComplexRationalLogCertificate

namespace OAI

/-! Exact rational intervals, logarithm bounds and arithmetic circuit soundness. -/

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
      (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
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
    _ ≤ (a.radius : ℝ) + |(a.center : ℝ) - (b.center : ℝ)| := add_le_add_left hx _
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

end OAI
