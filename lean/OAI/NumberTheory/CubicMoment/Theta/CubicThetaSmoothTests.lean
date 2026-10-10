import OAI.NumberTheory.CubicMoment.Theta.CubicThetaChartSections

namespace OAI

/-! Compact smooth sections and their actual Euclidean localizations.
The derivatives here are derivatives of the section, rather than extra
independent data attached to a test vector. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

def cubicThetaSmoothTests : Submodule ℂ CubicThetaSection where
  carrier := {F | ContDiffOn ℝ ∞ (fun y => F.val (cubicThetaPointInclusion.symm y))
      {y : ℂ × ℝ | 0<y.2} ∧ HasCompactSupport (cubicThetaSectionNorm F)}
  zero_mem' := by
    constructor
    · change ContDiffOn ℝ ∞ (fun _ : ℂ × ℝ => (0:ℂ)) _
      exact contDiffOn_const
    · change HasCompactSupport (fun _ : CubicThetaQuotient => ‖(0:ℂ)‖)
      have he : (fun _ : CubicThetaQuotient => ‖(0:ℂ)‖)=(0 : CubicThetaQuotient → ℝ) := by
        funext q
        exact norm_zero
      rw [he]
      exact HasCompactSupport.zero
  add_mem' := by
    rintro F G ⟨hF,hFc⟩ ⟨hG,hGc⟩
    refine ⟨hF.add hG,?_⟩
    apply (hFc.add hGc).mono'
    intro q hq
    contrapose! hq
    have hz : cubicThetaSectionNorm F q=0 ∧ cubicThetaSectionNorm G q=0 := by
      have h := image_eq_zero_of_notMem_tsupport hq
      exact ⟨(add_eq_zero_iff_of_nonneg (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp h |>.1,
        (add_eq_zero_iff_of_nonneg (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp h |>.2⟩
    simp only [Function.mem_support,not_not,cubicThetaSectionNorm,norm_eq_zero] at hz ⊢
    change F.val (cubicThetaQuotientLift q)+G.val (cubicThetaQuotientLift q)=0
    rw [hz.1,hz.2,add_zero]
  smul_mem' := by
    rintro c F ⟨hF,hFc⟩
    refine ⟨contDiffOn_const.mul hF,?_⟩
    apply hFc.mono'
    intro q hq
    contrapose! hq
    have hz := image_eq_zero_of_notMem_tsupport hq
    simp only [Function.mem_support,not_not]
    change ‖c*F.val (cubicThetaQuotientLift q)‖=0
    change ‖F.val (cubicThetaQuotientLift q)‖=0 at hz
    rw [norm_eq_zero] at hz
    rw [hz,mul_zero,norm_zero]

def cubicThetaTestLocalization (φ : ℂ × ℝ → ℂ) (F : CubicThetaSection)
    (y : ℂ × ℝ) : ℂ := φ y*F.val (cubicThetaPointInclusion.symm y)

lemma cubicThetaTestLocalization_smooth {φ : ℂ × ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hp : tsupport φ ⊆ {y : ℂ × ℝ | 0<y.2})
    (F : cubicThetaSmoothTests) : ContDiff ℝ ∞ (cubicThetaTestLocalization φ F) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : 0<y.2
  · exact (hφ.contDiffOn.mul F.property.1).contDiffAt
      ((isOpen_lt continuous_const continuous_snd).mem_nhds hy)
  · have hout : y∉tsupport (cubicThetaTestLocalization φ F) := by
      intro h
      exact hy (hp (tsupport_mul_subset_left h))
    exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℂ × ℝ => (0:ℂ)) y).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hout)

lemma cubicThetaTestLocalization_compact {φ : ℂ × ℝ → ℂ}
    (hφ : HasCompactSupport φ) (F : CubicThetaSection) :
    HasCompactSupport (cubicThetaTestLocalization φ F) := hφ.mul_right

lemma cubicThetaTestLocalization_derivative_memLp {φ : ℂ × ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hp : tsupport φ ⊆ {y : ℂ × ℝ | 0<y.2}) (F : cubicThetaSmoothTests) :
    MemLp (fderiv ℝ (cubicThetaTestLocalization φ F)) 2 (volume : Measure (ℂ × ℝ)) :=
  ((cubicThetaTestLocalization_smooth hφ hp F).continuous_fderiv (by simp)).memLp_of_hasCompactSupport
    ((cubicThetaTestLocalization_compact hc F).fderiv ℝ)

end CubicFirstMoment

end

end OAI
