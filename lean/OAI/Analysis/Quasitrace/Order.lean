import OAI.Analysis.Quasitrace.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Tactic.Linarith

namespace OAI

/-! Order preservation and pointwise bounds for normalized quasitraces. -/

section

noncomputable section
open scoped ComplexOrder
namespace Kaplansky
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Positivity on all positive elements follows from the square axiom. -/
theorem OneQuasitrace.map_nonneg (τ : OneQuasitrace A) {a : A} (ha : 0 ≤ a) :
    0 ≤ τ a := by
  obtain ⟨x, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
  exact τ.square_nonneg x

theorem OneQuasitrace.scalar_upper_bound (τ : OneQuasitrace A) (c : ℝ)
    {a : A} (ha : 0 ≤ a) (hca : a ≤ (c : ℂ) • (1 : A)) :
    (τ a).re ≤ c * (τ 1).re := by
  have h := τ.map_nonneg (sub_nonneg.mpr hca)
  rw [τ.map_scalar_sub (c : ℂ) ha.isSelfAdjoint] at h
  have hr : 0 ≤ ((c : ℂ) * τ 1 - τ a).re := h.1
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hr
  linarith

end Kaplansky

end
end

section

noncomputable section
open scoped ComplexOrder
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

theorem OneQuasitrace.unit_nonneg (τ : OneQuasitrace A) : 0 ≤ τ 1 := by
  simpa using τ.square_nonneg 1

/-- The scalar upper estimate also applies to arbitrary self-adjoints;
positivity is needed only for the scalar difference. -/
theorem OneQuasitrace.selfAdjoint_re_upper (τ : OneQuasitrace A)
    {a : A} (ha : IsSelfAdjoint a) : (τ a).re ≤ ‖a‖ * (τ 1).re := by
  have hle : a ≤ (‖a‖ : ℂ) • (1 : A) := by
    simpa only [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul] using
      ha.le_algebraMap_norm_self
  have hp := τ.map_nonneg (sub_nonneg.mpr hle)
  rw [τ.map_scalar_sub (‖a‖ : ℂ) ha] at hp
  have hr := hp.1
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re] at hr
  linarith

theorem OneQuasitrace.selfAdjoint_im_zero (τ : OneQuasitrace A)
    {a : A} (ha : IsSelfAdjoint a) : (τ a).im = 0 := by
  have hle : a ≤ (‖a‖ : ℂ) • (1 : A) := by
    simpa only [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul] using
      ha.le_algebraMap_norm_self
  have hp := τ.map_nonneg (sub_nonneg.mpr hle)
  rw [τ.map_scalar_sub (‖a‖ : ℂ) ha] at hp
  have hi := hp.2
  have hunit : (τ 1).im = 0 := by simpa using τ.unit_nonneg.2.symm
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, hunit, mul_zero, Complex.zero_im] at hi
  linarith

theorem OneQuasitrace.norm_selfAdjoint_le (τ : OneQuasitrace A)
    {a : A} (ha : IsSelfAdjoint a) : ‖τ a‖ ≤ ‖a‖ * (τ 1).re := by
  have hu := τ.selfAdjoint_re_upper ha
  have hl := τ.selfAdjoint_re_upper ha.neg
  rw [τ.map_neg ha, norm_neg, Complex.neg_re] at hl
  have he : τ a = ((τ a).re : ℂ) := by
    apply Complex.ext <;> simp [τ.selfAdjoint_im_zero ha]
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, hu⟩

/-- A uniform pointwise bound without global additivity or continuity of τ.
This supplies compact coordinate disks for the existence problem. -/
theorem OneQuasitrace.norm_le_twice (τ : OneQuasitrace A) (a : A) :
    ‖τ a‖ ≤ 2 * ‖a‖ * (τ 1).re := by
  have h := τ.real_imag (realPart a) (imaginaryPart a)
    (realPart a).property (imaginaryPart a).property
  rw [realPart_add_I_smul_imaginaryPart] at h
  rw [h]
  calc
    ‖τ (realPart a) + Complex.I * τ (imaginaryPart a)‖
        ≤ ‖τ (realPart a)‖ + ‖τ (imaginaryPart a)‖ := by
          simpa only [norm_mul, Complex.norm_I, one_mul] using
            norm_add_le (τ (realPart a)) (Complex.I * τ (imaginaryPart a))
    _ ≤ ‖(realPart a : A)‖ * (τ 1).re + ‖(imaginaryPart a : A)‖ * (τ 1).re :=
      add_le_add (τ.norm_selfAdjoint_le (realPart a).property)
        (τ.norm_selfAdjoint_le (imaginaryPart a).property)
    _ ≤ ‖a‖ * (τ 1).re + ‖a‖ * (τ 1).re :=
      add_le_add (mul_le_mul_of_nonneg_right (realPart.norm_le a) τ.unit_nonneg.1)
        (mul_le_mul_of_nonneg_right (imaginaryPart.norm_le a) τ.unit_nonneg.1)
    _ = 2 * ‖a‖ * (τ 1).re := by ring

theorem OneQuasitrace.normalized_norm_le (τ : OneQuasitrace A)
    (hτ : τ.Normalized) (a : A) : ‖τ a‖ ≤ 2 * ‖a‖ := by
  change τ 1 = 1 at hτ
  simpa only [hτ, Complex.one_re, mul_one] using τ.norm_le_twice a

end Kaplansky

end
end

end OAI
