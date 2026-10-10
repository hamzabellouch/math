import OAI.MathematicalPhysics.DefocusingNLS.Certificates.SeparatorArithmetic

namespace OAI

/-! # Sound Gaussian-integer error balls

The center is a Gaussian integer and the radius is an integer. The product
radius bounds the error arising from both factors.
-/

namespace DefocusingNLS

structure GaussianEnclosure where
  center : GaussianInt
  error : ℤ
  deriving DecidableEq

namespace GaussianEnclosure

def magnitude (z : GaussianInt) : ℤ := |z.re| + |z.im|

noncomputable def Encloses (a : GaussianEnclosure) (z : ℂ) : Prop :=
  ‖z - (a.center : ℂ)‖ ≤ (a.error : ℝ)

def add (a b : GaussianEnclosure) : GaussianEnclosure :=
  ⟨a.center + b.center, a.error + b.error⟩

def neg (a : GaussianEnclosure) : GaussianEnclosure := ⟨-a.center, a.error⟩

def mul (a b : GaussianEnclosure) : GaussianEnclosure :=
  ⟨a.center * b.center, a.error * (magnitude b.center + b.error) + magnitude a.center * b.error⟩

def conj (a : GaussianEnclosure) : GaussianEnclosure := ⟨star a.center, a.error⟩

theorem magnitude_nonneg (z : GaussianInt) : 0 ≤ magnitude z := add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem norm_center_le_magnitude (z : GaussianInt) : ‖(z : ℂ)‖ ≤ (magnitude z : ℝ) := by
  rw [GaussianInt.toComplex_def]
  apply (norm_add_le _ _).trans
  change ‖((z.re : ℝ) : ℂ)‖ + ‖((z.im : ℝ) : ℂ) * Complex.I‖ ≤ _
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
    magnitude, Int.cast_add, Int.cast_abs]
  exact le_rfl

theorem error_nonneg {a : GaussianEnclosure} {z : ℂ} (h : a.Encloses z) : 0 ≤ a.error := by
  have h' : (0 : ℝ) ≤ a.error := (norm_nonneg _).trans h
  exact_mod_cast h'

theorem add_sound {a b : GaussianEnclosure} {x y : ℂ} (ha : a.Encloses x) (hb : b.Encloses y) :
    (add a b).Encloses (x + y) := by
  change ‖x + y - ((a.center + b.center : GaussianInt) : ℂ)‖ ≤ ((a.error + b.error : ℤ) : ℝ)
  rw [GaussianInt.toComplex_add, Int.cast_add]
  calc
    _ = ‖(x - (a.center : ℂ)) + (y - (b.center : ℂ))‖ := by congr 1; ring
    _ ≤ ‖x - (a.center : ℂ)‖ + ‖y - (b.center : ℂ)‖ := norm_add_le _ _
    _ ≤ _ := add_le_add ha hb

theorem neg_sound {a : GaussianEnclosure} {z : ℂ} (h : a.Encloses z) : (neg a).Encloses (-z) := by
  change ‖-z - ((-a.center : GaussianInt) : ℂ)‖ ≤ (a.error : ℝ)
  rw [GaussianInt.toComplex_neg]
  calc
    _ = ‖-(z - (a.center : ℂ))‖ := by congr 1; ring
    _ = ‖z - (a.center : ℂ)‖ := norm_neg _
    _ ≤ _ := h

theorem conj_sound {a : GaussianEnclosure} {z : ℂ} (h : a.Encloses z) : (conj a).Encloses (star z) := by
  change ‖star z - ((star a.center : GaussianInt) : ℂ)‖ ≤ (a.error : ℝ)
  rw [GaussianInt.toComplex_star]
  change ‖star z - star (a.center : ℂ)‖ ≤ _
  rw [← star_sub, norm_star]
  exact h

theorem mul_sound {a b : GaussianEnclosure} {x y : ℂ} (ha : a.Encloses x) (hb : b.Encloses y) :
    (mul a b).Encloses (x * y) := by
  have hae : (0 : ℝ) ≤ a.error := by exact_mod_cast error_nonneg ha
  have hbe : (0 : ℝ) ≤ b.error := by exact_mod_cast error_nonneg hb
  have ham := norm_center_le_magnitude a.center
  have hbm := norm_center_le_magnitude b.center
  change ‖x * y - ((a.center * b.center : GaussianInt) : ℂ)‖ ≤ _
  rw [GaussianInt.toComplex_mul]
  calc
    _ = ‖(x - (a.center : ℂ)) * (y - (b.center : ℂ)) +
        (x - (a.center : ℂ)) * (b.center : ℂ) +
          (a.center : ℂ) * (y - (b.center : ℂ))‖ := by congr 1; ring
    _ ≤ (‖(x - (a.center : ℂ)) * (y - (b.center : ℂ))‖ +
        ‖(x - (a.center : ℂ)) * (b.center : ℂ)‖) +
          ‖(a.center : ℂ) * (y - (b.center : ℂ))‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ((a.error : ℝ) * b.error + a.error * (magnitude b.center : ℝ)) +
        (magnitude a.center : ℝ) * b.error := by
      simp only [norm_mul]
      exact add_le_add
        (add_le_add (mul_le_mul ha hb (norm_nonneg _) hae)
          (mul_le_mul ha hbm (norm_nonneg _) hae))
        (mul_le_mul ham hb (norm_nonneg _) (by exact_mod_cast magnitude_nonneg a.center))
    _ = _ := by simp only [mul, Int.cast_add, Int.cast_mul]; ring

end GaussianEnclosure

end DefocusingNLS

end OAI
