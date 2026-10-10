import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousComplexCoordinates

namespace OAI

/-! # Complexification of actual real-linear operators on Y

The doubled complex space uses its existing product norm. The factor two
in the norm estimate is harmless for the later fixed long-time contraction.
-/

namespace DefocusingNLS

section

variable (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)

local notation "H" => HomogeneousY a k
local notation "J" => homogeneousConjugation a k ha ha1 hk
local notation "X" => homogeneousComplexReal a k ha ha1 hk
local notation "Y" => homogeneousComplexImag a k ha ha1 hk

noncomputable def homogeneousComplexificationReal (T : H →L[ℝ] H) :
    (H × H) →L[ℝ] H × H :=
  (T.comp X + Complex.I • T.comp Y).prod
    ((J).comp (T.comp X) + Complex.I • (J).comp (T.comp Y))

@[simp] theorem homogeneousComplexificationReal_apply (T : H →L[ℝ] H) (z : H × H) :
    homogeneousComplexificationReal a k ha ha1 hk T z =
      (T (X z) + Complex.I • T (Y z), J (T (X z)) + Complex.I • J (T (Y z))) := rfl

theorem homogeneousComplexificationReal_I (T : H →L[ℝ] H) (z : H × H) :
    homogeneousComplexificationReal a k ha ha1 hk T (Complex.I • z) =
      Complex.I • homogeneousComplexificationReal a k ha ha1 hk T z := by
  apply Prod.ext
  all_goals
    simp only [homogeneousComplexificationReal_apply, homogeneousComplexReal_I,
      homogeneousComplexImag_I, map_neg, Prod.smul_fst, Prod.smul_snd, smul_add, smul_smul]
    match_scalars
    all_goals ring_nf
    all_goals norm_num [Complex.I_sq]

noncomputable def homogeneousComplexification (T : H →L[ℝ] H) :
    (H × H) →L[ℂ] H × H where
  toFun := homogeneousComplexificationReal a k ha ha1 hk T
  map_add' := map_add (homogeneousComplexificationReal a k ha ha1 hk T)
  map_smul' := by
    intro c z
    let C := homogeneousComplexificationReal a k ha ha1 hk T
    change C (c • z) = c • C z
    calc
      C (c • z) = C (c.re • z + c.im • (Complex.I • z)) := by
        apply congrArg C
        conv_lhs => rw [← c.re_add_im]
        simp only [add_smul, mul_smul, Complex.coe_smul]
        rfl
      _ = c.re • C z + c.im • C (Complex.I • z) := by
        rw [map_add, C.map_smul, C.map_smul]
      _ = c.re • C z + c.im • (Complex.I • C z) := by
        rw [homogeneousComplexificationReal_I]
      _ = c • C z := by
        conv_rhs => rw [← c.re_add_im]
        simp only [add_smul, mul_smul, Complex.coe_smul]
        rfl
  cont := (homogeneousComplexificationReal a k ha ha1 hk T).continuous

@[simp] theorem homogeneousComplexification_apply (T : H →L[ℝ] H) (z : H × H) :
    homogeneousComplexification a k ha ha1 hk T z =
      (T (X z) + Complex.I • T (Y z), J (T (X z)) + Complex.I • J (T (Y z))) := rfl

theorem homogeneousComplexification_real (T : H →L[ℝ] H) (z : H × H) :
    X (homogeneousComplexification a k ha ha1 hk T z) = T (X z) := by
  simp only [homogeneousComplexReal_apply, homogeneousComplexification_apply,
    homogeneousConjugation_complex_smul, map_add, homogeneousConjugation_involutive,
    Complex.conj_I]
  match_scalars <;> ring_nf

theorem homogeneousComplexification_imag (T : H →L[ℝ] H) (z : H × H) :
    Y (homogeneousComplexification a k ha ha1 hk T z) = T (Y z) := by
  simp only [homogeneousComplexImag_apply, homogeneousComplexification_apply,
    homogeneousConjugation_complex_smul, map_add, homogeneousConjugation_involutive,
    Complex.conj_I, smul_add, smul_sub, smul_smul]
  match_scalars
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]

@[simp] theorem homogeneousComplexification_id :
    homogeneousComplexification a k ha ha1 hk (ContinuousLinearMap.id ℝ H) =
      ContinuousLinearMap.id ℂ (H × H) := by
  apply ContinuousLinearMap.ext
  intro z
  change (X z + Complex.I • Y z, J (X z) + Complex.I • J (Y z)) = z
  apply Prod.ext
  · exact homogeneousComplexCoordinates_first a k ha ha1 hk z
  · exact homogeneousComplexCoordinates_second a k ha ha1 hk z

theorem homogeneousComplexification_comp (T S : H →L[ℝ] H) :
    homogeneousComplexification a k ha ha1 hk (T.comp S) =
      (homogeneousComplexification a k ha ha1 hk T).comp
        (homogeneousComplexification a k ha ha1 hk S) := by
  apply ContinuousLinearMap.ext
  intro z
  change homogeneousComplexification a k ha ha1 hk (T.comp S) z =
    homogeneousComplexification a k ha ha1 hk T
      (homogeneousComplexification a k ha ha1 hk S z)
  rw [homogeneousComplexification_apply, homogeneousComplexification_apply,
    homogeneousComplexification_real, homogeneousComplexification_imag]
  rfl

theorem homogeneousComplexification_add (T S : H →L[ℝ] H) :
    homogeneousComplexification a k ha ha1 hk (T + S) =
      homogeneousComplexification a k ha ha1 hk T +
        homogeneousComplexification a k ha ha1 hk S := by
  apply ContinuousLinearMap.ext
  intro z
  apply Prod.ext <;>
    simp only [homogeneousComplexification_apply, add_apply,
      Prod.fst_add, Prod.snd_add, map_add, smul_add] <;> match_scalars <;> ring_nf

theorem homogeneousComplexification_apply_norm_le (T : H →L[ℝ] H) (z : H × H) :
    ‖homogeneousComplexification a k ha ha1 hk T z‖ ≤ 2 * ‖T‖ * ‖z‖ := by
  have hX := homogeneousComplexReal_norm_le a k ha ha1 hk z
  have hY := homogeneousComplexImag_norm_le a k ha ha1 hk z
  have hTX : ‖T (X z)‖ ≤ ‖T‖ * ‖z‖ :=
    (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left hX (norm_nonneg T))
  have hTY : ‖T (Y z)‖ ≤ ‖T‖ * ‖z‖ :=
    (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left hY (norm_nonneg T))
  rw [homogeneousComplexification_apply, Prod.norm_def]
  apply max_le
  · have h := norm_add_le (T (X z)) (Complex.I • T (Y z))
    simp only [norm_smul, Complex.norm_I, one_mul] at h
    linarith
  · have h := norm_add_le (J (T (X z))) (Complex.I • J (T (Y z)))
    simp only [norm_smul, Complex.norm_I, one_mul, homogeneousConjugation_norm] at h
    linarith

theorem homogeneousComplexification_norm_le (T : H →L[ℝ] H) :
    ‖homogeneousComplexification a k ha ha1 hk T‖ ≤ 2 * ‖T‖ := by
  exact ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (homogeneousComplexification_apply_norm_le a k ha ha1 hk T)

end

end DefocusingNLS

end OAI
