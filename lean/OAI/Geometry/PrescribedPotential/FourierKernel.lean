import Mathlib
import OAI.Geometry.PrescribedPotential.SobolevParametrix

namespace OAI

/-! Fourier Kernel. -/

section

 
noncomputable section
open MeasureTheory Set Filter Topology FourierTransform
open scoped BoundedContinuousFunction SchwartzMap Classical Real ComplexInnerProductSpace
namespace EllipticCompact
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
open SobolevChart

lemma phase_sub_bound (a b : ℝ) :
    ‖((Real.fourierChar a : Circle) : ℂ) - (Real.fourierChar b : Circle)‖ ≤ 2 * Real.pi * ‖a - b‖ := by
  have he : ((Real.fourierChar a : Circle) : ℂ) - (Real.fourierChar b : Circle) =
      (((Real.fourierChar (a-b) : Circle) : ℂ) - 1) * (Real.fourierChar b : Circle) := by
    rw [sub_mul, one_mul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    rw [sub_add_cancel]
  rw [he, norm_mul, Circle.norm_coe, mul_one, Real.fourierChar_apply]
  have hb := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * (a-b))
  rw [mul_comm (Complex.I)] at hb
  exact hb.trans (by simp only [norm_mul, Real.norm_eq_abs, abs_of_pos Real.pi_pos]; norm_num)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma phase_inner_sub_bound (x z y : E) :
    ‖((Real.fourierChar (inner ℝ y x) : Circle) : ℂ) -
      (Real.fourierChar (inner ℝ y z) : Circle)‖ ≤ 2 * Real.pi * ‖y‖ * ‖x-z‖ := by
  apply (phase_sub_bound _ _).trans
  rw [← inner_sub_right]
  calc
    _ ≤ (2 * Real.pi) * (‖y‖ * ‖x-z‖) :=
      mul_le_mul_of_nonneg_left (norm_inner_le_norm y (x-z))
        (mul_nonneg (by norm_num) Real.pi_pos.le)
    _ = _ := by ring

def kernelSectionFun (χ : 𝓢(E, ℂ)) (x y : E) : ℂ :=
  star (((Real.fourierChar (inner ℝ y x) : Circle) : ℂ) * χ y)

lemma kernelSection_memLp (χ : 𝓢(E, ℂ)) (x : E) :
    MemLp (kernelSectionFun χ x) 2 (volume : Measure E) := by
  apply (χ.memLp (p := 2) (μ := volume)).mono
    (show Continuous (kernelSectionFun χ x) by
      unfold kernelSectionFun
      exact ((continuous_subtype_val.comp (Real.continuous_fourierChar.comp
        (continuous_id.inner continuous_const))).mul χ.continuous).star
      ).aestronglyMeasurable
  filter_upwards [] with y
  simp only [kernelSectionFun, norm_star, norm_mul, Circle.norm_coe, one_mul, le_refl]

def kernelSection (χ : 𝓢(E, ℂ)) (x : E) : L2 E :=
  (kernelSection_memLp χ x).toLp (kernelSectionFun χ x)

lemma kernelSection_ae (χ : 𝓢(E, ℂ)) (x : E) :
    kernelSection χ x =ᵐ[volume] kernelSectionFun χ x :=
  (kernelSection_memLp χ x).coeFn_toLp

lemma kernelSection_continuous (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport χ) :
    Continuous (kernelSection χ) := by
  obtain ⟨R, hR, hbound⟩ := hχ.isBounded.exists_pos_norm_le
  have hb (x z : E) : ‖kernelSection χ x - kernelSection χ z‖ ≤
      (2 * Real.pi * R * ‖χ.toLp 2‖) * ‖x-z‖ := by
    calc
      ‖kernelSection χ x - kernelSection χ z‖ ≤
          (2 * Real.pi * R * ‖x-z‖) * ‖χ.toLp 2‖ := by
        apply Lp.norm_le_mul_norm_of_ae_le_mul
        filter_upwards [Lp.coeFn_sub (kernelSection χ x) (kernelSection χ z),
          kernelSection_ae χ x, kernelSection_ae χ z, χ.coeFn_toLp 2 volume] with y hs hx hz hχy
        rw [hs, Pi.sub_apply, hx, hz, hχy]
        simp only [kernelSectionFun, ← star_sub, ← sub_mul, norm_star, norm_mul]
        by_cases hy : χ y = 0
        · simp [hy]
        · apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact (phase_inner_sub_bound x z y).trans
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
              (hbound y (subset_tsupport _ hy)) (by positivity)) (norm_nonneg _))
      _ = _ := by ring
  apply LipschitzWith.continuous (K := ⟨2 * Real.pi * R * ‖χ.toLp 2‖, by positivity⟩)
  apply LipschitzWith.of_dist_le_mul
  intro x z
  rw [dist_eq_norm, dist_eq_norm]
  exact hb x z

end EllipticCompact

end
end

end OAI
