import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

namespace OAI

/-! # Removing the pole in the modular strip contour

The scalar contour step in Rieffel--Van Daele, Lemma 4.6, uses
`(exp (i φ z) f z - f 0) / sin (π z)`. Divided differences remove its
singularity at zero without assuming a residue theorem.
-/

namespace KadisonKastler

open Set Filter
open scoped Topology

noncomputable section

def stripSineSlope (z : ℂ) : ℂ :=
  dslope (fun w : ℂ => Complex.sin (Real.pi * w)) 0 z

theorem stripSineSlope_ne_zero {z : ℂ} (hz : |z.re| < 1) :
    stripSineSlope z ≠ 0 := by
  by_cases hz0 : z = 0
  · subst z
    unfold stripSineSlope
    rw [dslope_same]
    have hd := ((hasDerivAt_id (0 : ℂ)).const_mul (Real.pi : ℂ)).csin
    have he : deriv (fun w : ℂ => Complex.sin (Real.pi * w)) 0 = (Real.pi : ℂ) := by
      simpa only [id_eq, mul_zero, Complex.cos_zero, mul_one, one_mul] using hd.deriv
    rw [he]
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  · have hs : Complex.sin (Real.pi * z) ≠ 0 := by
      intro he
      obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp he
      have hzk : z = (k : ℂ) := by
        apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
        exact hk.trans (mul_comm _ _)
      have hk' : (-1 : ℝ) < k ∧ (k : ℝ) < 1 := by simpa [hzk] using abs_lt.mp hz
      have hk0 : k = 0 := by
        have h₁ : (-1 : ℤ) < k := by exact_mod_cast hk'.1
        have h₂ : k < (1 : ℤ) := by exact_mod_cast hk'.2
        omega
      exact hz0 (by simpa [hk0] using hzk)
    unfold stripSineSlope
    rw [dslope_of_ne _ hz0]
    simp only [slope, sub_zero, mul_zero, Complex.sin_zero, smul_eq_mul, vsub_eq_sub]
    exact mul_ne_zero (inv_ne_zero hz0) hs

theorem stripSineSlope_differentiable : Differentiable ℂ stripSineSlope := by
  apply differentiableOn_univ.mp
  exact (Complex.differentiableOn_dslope (mem_nhds_iff.mpr ⟨univ,
    subset_rfl, isOpen_univ, mem_univ _⟩)).mpr (by fun_prop)

def stripSineQuotient (φ : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  dslope (fun w => Complex.exp (Complex.I * φ * w) * f w) 0 z / stripSineSlope z

theorem stripSineQuotient_eq {φ : ℝ} {f : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0) :
    stripSineQuotient φ f z =
      (Complex.exp (Complex.I * φ * z) * f z - f 0) / Complex.sin (Real.pi * z) := by
  unfold stripSineQuotient stripSineSlope
  rw [dslope_of_ne _ hz, dslope_of_ne _ hz]
  simp only [slope, sub_zero, mul_zero, Complex.exp_zero, one_mul, Complex.sin_zero,
    smul_eq_mul, vsub_eq_sub]
  exact mul_div_mul_left _ _ (inv_ne_zero hz)

theorem stripSineQuotient_differentiableOn (φ : ℝ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f {z : ℂ | |z.re| < 1 / 2}) :
    DifferentiableOn ℂ (stripSineQuotient φ f) {z : ℂ | |z.re| < 1 / 2} := by
  have h0 : {z : ℂ | |z.re| < 1 / 2} ∈ 𝓝 (0 : ℂ) := by
    apply (isOpen_lt (Complex.continuous_re.abs) continuous_const).mem_nhds
    norm_num
  apply DifferentiableOn.div _ stripSineSlope_differentiable.differentiableOn
    (fun z hz => stripSineSlope_ne_zero (lt_trans hz (by norm_num)))
  apply (Complex.differentiableOn_dslope h0).mpr
  exact (by fun_prop : Differentiable ℂ (fun w : ℂ => Complex.exp (Complex.I * φ * w))).differentiableOn.mul hf

theorem stripSineQuotient_continuousOn (φ : ℝ) (f : ℂ → ℂ)
    (hc : ContinuousOn f {z : ℂ | |z.re| ≤ 1 / 2})
    (hd : DifferentiableAt ℂ f 0) :
    ContinuousOn (stripSineQuotient φ f) {z : ℂ | |z.re| ≤ 1 / 2} := by
  apply ContinuousOn.div _ stripSineSlope_differentiable.continuous.continuousOn
    (fun z hz => stripSineSlope_ne_zero (lt_of_le_of_lt hz (by norm_num)))
  intro z hz
  by_cases h : z = 0
  · subst z
    exact (continuousAt_dslope_same.mpr ((by fun_prop :
      DifferentiableAt ℂ (fun w : ℂ => Complex.exp (Complex.I * φ * w)) 0).mul hd)).continuousWithinAt
  · exact (continuousWithinAt_dslope_of_ne h).mpr
      ((by fun_prop : Continuous (fun w : ℂ => Complex.exp (Complex.I * φ * w))).continuousWithinAt.mul (hc z hz))

end

end KadisonKastler

end OAI
