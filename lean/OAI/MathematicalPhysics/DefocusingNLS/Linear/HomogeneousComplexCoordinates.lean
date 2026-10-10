import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousConjugation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalInjective

namespace OAI

/-! # Concrete complexification coordinates for the faithful homogeneous space

The two complex channels encode x+i y by (x+i y, J x+i J y), where J is
physical conjugation. Both real coordinates are bounded by the product norm.
-/

open scoped ComplexConjugate

namespace DefocusingNLS

section

variable (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)

local notation "H" => HomogeneousY a k
local notation "J" => homogeneousConjugation a k ha ha1 hk

theorem homogeneousConjugation_complex_smul (c : ℂ) (f : H) :
    J (c • f) = conj c • J f := by
  apply homogeneousPhysicalCLM_injective a k ha ha1 hk
  apply DFunLike.ext
  intro x
  simp only [homogeneousConjugation_physical, map_smul,
    ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul, map_mul]

noncomputable def homogeneousComplexReal : (H × H) →L[ℝ] H :=
  (1 / 2 : ℂ) • (ContinuousLinearMap.fst ℝ H H +
    (J).comp (ContinuousLinearMap.snd ℝ H H))

noncomputable def homogeneousComplexImag : (H × H) →L[ℝ] H :=
  (-Complex.I / 2 : ℂ) • (ContinuousLinearMap.fst ℝ H H -
    (J).comp (ContinuousLinearMap.snd ℝ H H))

@[simp] theorem homogeneousComplexReal_apply (z : H × H) :
    homogeneousComplexReal a k ha ha1 hk z = (1 / 2 : ℂ) • (z.1 + J z.2) := rfl

@[simp] theorem homogeneousComplexImag_apply (z : H × H) :
    homogeneousComplexImag a k ha ha1 hk z = (-Complex.I / 2 : ℂ) • (z.1 - J z.2) := rfl

theorem homogeneousComplexCoordinates_first (z : H × H) :
    homogeneousComplexReal a k ha ha1 hk z +
      Complex.I • homogeneousComplexImag a k ha ha1 hk z = z.1 := by
  simp only [homogeneousComplexReal_apply, homogeneousComplexImag_apply, smul_smul]
  have hc : Complex.I * (-Complex.I / 2) = (1 / 2 : ℂ) := by
    norm_num [div_eq_mul_inv, ← mul_assoc]
  rw [hc]
  match_scalars <;> norm_num

theorem homogeneousComplexCoordinates_second (z : H × H) :
    J (homogeneousComplexReal a k ha ha1 hk z) +
      Complex.I • J (homogeneousComplexImag a k ha ha1 hk z) = z.2 := by
  simp only [homogeneousComplexReal_apply, homogeneousComplexImag_apply,
    homogeneousConjugation_complex_smul, map_add, map_sub, homogeneousConjugation_involutive]
  simp only [smul_smul]
  have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := map_natCast (starRingEnd ℂ) 2
  match_scalars <;>
    simp only [map_div₀, map_neg, Complex.conj_I, map_one, htwo] <;> ring_nf <;> norm_num

theorem homogeneousComplexReal_I (z : H × H) :
    homogeneousComplexReal a k ha ha1 hk (Complex.I • z) =
      -homogeneousComplexImag a k ha ha1 hk z := by
  simp only [homogeneousComplexReal_apply, homogeneousComplexImag_apply,
    Prod.smul_fst, Prod.smul_snd, homogeneousConjugation_complex_smul, Complex.conj_I]
  module

theorem homogeneousComplexImag_I (z : H × H) :
    homogeneousComplexImag a k ha ha1 hk (Complex.I • z) =
      homogeneousComplexReal a k ha ha1 hk z := by
  simp only [homogeneousComplexReal_apply, homogeneousComplexImag_apply,
    Prod.smul_fst, Prod.smul_snd, homogeneousConjugation_complex_smul, Complex.conj_I]
  simp only [smul_sub, smul_add, smul_smul]
  match_scalars <;> ring_nf <;> norm_num

theorem homogeneousComplexReal_norm_le (z : H × H) :
    ‖homogeneousComplexReal a k ha ha1 hk z‖ ≤ ‖z‖ := by
  rw [homogeneousComplexReal_apply, norm_smul]
  have hc : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hc]
  have he := norm_add_le z.1 (J z.2)
  rw [homogeneousConjugation_norm] at he
  nlinarith [norm_fst_le z, norm_snd_le z]

theorem homogeneousComplexImag_norm_le (z : H × H) :
    ‖homogeneousComplexImag a k ha ha1 hk z‖ ≤ ‖z‖ := by
  rw [homogeneousComplexImag_apply, norm_smul]
  have hc : ‖(-Complex.I / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hc]
  have he := norm_sub_le z.1 (J z.2)
  rw [homogeneousConjugation_norm] at he
  nlinarith [norm_fst_le z, norm_snd_le z]

end

end DefocusingNLS

end OAI
