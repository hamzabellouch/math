import OAI.NumberTheory.CubicMoment.Estimates.ShrinkingProfile
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

namespace OAI

/-! Bounded derivatives of the fixed smooth step, before narrowing the
transition in the logarithmic prime cutoff. -/
noncomputable section
open Set
open scoped ContDiff SchwartzMap
namespace CubicFirstMoment

def primeSmoothStep (x : ℝ) : ℂ := (Real.smoothTransition x:ℂ)

lemma primeSmoothStep_smooth : ContDiff ℝ ∞ primeSmoothStep :=
  Complex.ofRealCLM.contDiff.comp Real.smoothTransition.contDiff

lemma primeSmoothStep_norm (x : ℝ) : ‖primeSmoothStep x‖ ≤ 1 := by
  rw [primeSmoothStep,Complex.norm_real,Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

lemma primeSmoothStep_deriv_zero {x : ℝ} (hx : x ∉ Icc (0:ℝ) 1) :
    deriv primeSmoothStep x=0 := by
  by_cases hlo : x < 0
  · have he : EqOn primeSmoothStep (fun _ : ℝ => (0:ℂ)) (Iio 0) := by
      intro y hy
      simp only [primeSmoothStep,Real.smoothTransition.zero_of_nonpos hy.le,Complex.ofReal_zero]
    simpa only [deriv_const] using he.deriv isOpen_Iio hlo
  · have hhi : 1 < x := by
      have hh : ¬(0 ≤ x ∧ x ≤ 1) := hx
      have : 0 ≤ x := le_of_not_gt hlo
      exact lt_of_not_ge (fun h => hh ⟨this,h⟩)
    have he : EqOn primeSmoothStep (fun _ : ℝ => (1:ℂ)) (Ioi 1) := by
      intro y hy
      simp only [primeSmoothStep,Real.smoothTransition.one_of_one_le hy.le,Complex.ofReal_one]
    simpa only [deriv_const] using he.deriv isOpen_Ioi hhi

lemma primeSmoothStep_deriv_compact : HasCompactSupport (deriv primeSmoothStep) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (0:ℝ)) (b := 1))
  intro x hx
  by_contra hn
  exact hx (primeSmoothStep_deriv_zero hn)

def primeSmoothStepDerivative : 𝓢(ℝ,ℂ) :=
  primeSmoothStep_deriv_compact.toSchwartzMap (contDiff_infty_iff_deriv.mp primeSmoothStep_smooth).2

lemma primeSmoothStep_derivatives_bounded (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖iteratedFDeriv ℝ n primeSmoothStep x‖ ≤ C := by
  cases n with
  | zero =>
    refine ⟨1,by norm_num,?_⟩
    intro x
    simpa only [norm_iteratedFDeriv_zero] using primeSmoothStep_norm x
  | succ n =>
    refine ⟨SchwartzMap.seminorm ℝ 0 n primeSmoothStepDerivative,by positivity,?_⟩
    intro x
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_succ']
    have h := SchwartzMap.le_seminorm ℝ 0 n primeSmoothStepDerivative x
    simpa only [pow_zero,one_mul,norm_iteratedFDeriv_eq_norm_iteratedDeriv] using! h

lemma smoothStep_affine_deriv_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (J c x : ℝ), 0 ≤ J →
      ‖iteratedFDeriv ℝ n (fun y => primeSmoothStep (J*(y-c))) x‖ ≤ C*J^n := by
  obtain ⟨C,hC,hb⟩ := primeSmoothStep_derivatives_bounded n
  refine ⟨C,hC,?_⟩
  intro J c x hJ
  have he : (fun y => primeSmoothStep (J*(y-c)))=
      fun y => (fun z => primeSmoothStep (J • z)) (y-c) := rfl
  rw [he,iteratedFDeriv_comp_sub_real (fun z : ℝ => primeSmoothStep (J • z)) c n,
    iteratedFDeriv_comp_const_smul J (primeSmoothStep_smooth.of_le (by simp)),
    norm_smul,Real.norm_eq_abs,abs_pow,abs_of_nonneg hJ]
  simpa only [smul_eq_mul,mul_comm C] using mul_le_mul_of_nonneg_left (hb (J*(x-c))) (pow_nonneg hJ n)

end CubicFirstMoment

end

end OAI
