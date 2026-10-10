import OAI.NumberTheory.CubicMoment.Estimates.PrimeSmoothTransition

namespace OAI

/-! A genuine smooth approximation to the dyadic interval in logarithmic
coordinates. The two endpoint transitions have width exactly 1/J. -/
noncomputable section
open Set
open scoped ContDiff SchwartzMap
namespace CubicFirstMoment

def primeLogWindow (J u : ℝ) : ℂ :=
  primeSmoothStep (J*(u+Real.log 2)+1)-primeSmoothStep (J*u)

lemma primeLogWindow_smooth (J : ℝ) : ContDiff ℝ ∞ (primeLogWindow J) :=
  (primeSmoothStep_smooth.comp (by fun_prop)).sub (primeSmoothStep_smooth.comp (by fun_prop))

lemma primeLogWindow_one {J u : ℝ} (hJ : 0 ≤ J)
    (hu : -Real.log 2 ≤ u ∧ u ≤ 0) : primeLogWindow J u=1 := by
  have hlo : 1 ≤ J*(u+Real.log 2)+1 := by nlinarith
  have hhi : J*u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hJ hu.2
  simp only [primeLogWindow,primeSmoothStep,Real.smoothTransition.one_of_one_le hlo,
    Real.smoothTransition.zero_of_nonpos hhi,Complex.ofReal_one,Complex.ofReal_zero,sub_zero]

lemma primeLogWindow_zero_left {J u : ℝ} (hJ : 0 < J)
    (hu : u ≤ -Real.log 2-1/J) : primeLogWindow J u=0 := by
  have hlo : J*(u+Real.log 2)+1 ≤ 0 := by
    have hh := mul_le_mul_of_nonneg_left hu hJ.le
    have he : J*(-Real.log 2-1/J) = -J*Real.log 2-1 := by field_simp
    rw [he] at hh
    nlinarith
  have hhi : J*u ≤ 0 := by
    have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith
  simp only [primeLogWindow,primeSmoothStep,Real.smoothTransition.zero_of_nonpos hlo,
    Real.smoothTransition.zero_of_nonpos hhi,Complex.ofReal_zero,sub_self]

lemma primeLogWindow_zero_right {J u : ℝ} (hJ : 0 < J)
    (hu : 1/J ≤ u) : primeLogWindow J u=0 := by
  have hhi : 1 ≤ J*u := by
    have hh := mul_le_mul_of_nonneg_left hu hJ.le
    have he : J*(1/J)=1 := by field_simp
    rwa [he] at hh
  have hlo : 1 ≤ J*(u+Real.log 2)+1 := by
    have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith
  simp only [primeLogWindow,primeSmoothStep,Real.smoothTransition.one_of_one_le hlo,
    Real.smoothTransition.one_of_one_le hhi,Complex.ofReal_one,sub_self]

lemma primeLogWindow_support {J : ℝ} (hJ : 0 < J) :
    Function.support (primeLogWindow J) ⊆ Icc (-Real.log 2-1/J) (1/J) := by
  intro u hu
  constructor
  · by_contra h
    exact hu (primeLogWindow_zero_left hJ (le_of_lt (lt_of_not_ge h)))
  · by_contra h
    exact hu (primeLogWindow_zero_right hJ (le_of_lt (lt_of_not_ge h)))

lemma primeLogWindow_tsupport {J : ℝ} (hJ : 0 < J) :
    tsupport (primeLogWindow J) ⊆ Icc (-Real.log 2-1/J) (1/J) :=
  closure_minimal (primeLogWindow_support hJ) isClosed_Icc

lemma primeLogWindow_compact {J : ℝ} (hJ : 0 < J) : HasCompactSupport (primeLogWindow J) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (primeLogWindow_support hJ)

def primeLogWindowSchwartz (J : ℝ) (hJ : 0 < J) : 𝓢(ℝ,ℂ) :=
  (primeLogWindow_compact hJ).toSchwartzMap (primeLogWindow_smooth J)

lemma primeLogWindow_support_two {J u : ℝ} (hJ : 1 ≤ J)
    (hu : u ∈ tsupport (primeLogWindow J)) : |u| ≤ 2 := by
  have hp : 0 < J := by linarith
  have hi : 1/J ≤ 1 := (div_le_one hp).mpr hJ
  have hl : Real.log 2 ≤ 1 := by
    simpa only [show (2:ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  obtain ⟨hhlo,hhhi⟩ := primeLogWindow_tsupport hp hu
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma primeLogWindow_derivative_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ J u : ℝ, 1 ≤ J →
      ‖iteratedFDeriv ℝ n (primeLogWindow J) u‖ ≤ C*J^n := by
  obtain ⟨C,hC,hb⟩ := smoothStep_affine_deriv_bound n
  refine ⟨2*C,by positivity,?_⟩
  intro J u hJ
  have hp : 0 < J := by linarith
  let c : ℝ := -Real.log 2-1/J
  have he : primeLogWindow J=(fun y => primeSmoothStep (J*(y-c)))-
      (fun y => primeSmoothStep (J*(y-0))) := by
    funext y
    have hh : J*(y-c)=J*(y+Real.log 2)+1 := by dsimp [c]; field_simp; ring
    simp only [primeLogWindow,Pi.sub_apply,hh,sub_zero]
  have hf : ContDiff ℝ n (fun y : ℝ => primeSmoothStep (J*(y-c))) :=
    (primeSmoothStep_smooth.comp (by fun_prop)).of_le (by simp)
  have hg : ContDiff ℝ n (fun y : ℝ => primeSmoothStep (J*(y-0))) :=
    (primeSmoothStep_smooth.comp (by fun_prop)).of_le (by simp)
  rw [he,iteratedFDeriv_sub hf hg,Pi.sub_apply]
  exact (norm_sub_le _ _).trans (by nlinarith [hb J c u hp.le,hb J 0 u hp.le])

end CubicFirstMoment

end

end OAI
