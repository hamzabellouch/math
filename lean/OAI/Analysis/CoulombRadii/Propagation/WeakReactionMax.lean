import Mathlib
import OAI.Analysis.CoulombRadii.Propagation.TfReaction
import OAI.Analysis.CoulombRadii.Propagation.MaximumMollifier

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

theorem WeakLaplacianGE.max_reaction {f g b : Position → ℝ} {F : Position → ℝ → ℝ}
    {U : Set Position} (hU : IsOpen U) (hf : Continuous f) (hg : Continuous g)
    (hq : LocallyIntegrable (fun x => b x+F x (f x)) volume)
    (hr : LocallyIntegrable (fun x => b x+F x (g x)) volume)
    (hbq : ∀ R : ℝ, ∃ C : ℝ, ∀ x ∈ Metric.closedBall 0 R, |b x+F x (f x)| ≤ C)
    (hbr : ∀ R : ℝ, ∃ C : ℝ, ∀ x ∈ Metric.closedBall 0 R, |b x+F x (g x)| ≤ C)
    (hwf : WeakLaplacianGE f U (fun x => b x+F x (f x)))
    (hwg : WeakLaplacianGE g U (fun x => b x+F x (g x))) :
    WeakLaplacianGE (fun x => max (f x) (g x)) U (fun x => b x+F x (max (f x) (g x))) := by
  have H := WeakLaplacianGE.max_tied hU hf hg hq hr hbq hbr hwf hwg (fun x h => by rw [h])
  convert H using 1
  funext x
  by_cases h : g x ≤ f x
  · simp [h]
  · simp [h,max_eq_right (le_of_not_ge h)]

lemma cutoffReaction_offset_ball_bound {a Z : ℝ} (ha : 0 < a)
    {f : Position → ℝ} (hf : Continuous f) (R : ℝ) :
    ∃ C : ℝ, ∀ x ∈ Metric.closedBall 0 R,
      |cutoffReaction a (fun y => Z*coulombKernel y+f y) x| ≤ C := by
  obtain ⟨D,hD⟩ := (isCompact_closedBall (0:Position) R).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨tfReaction (|Z|/a+D),?_⟩
  intro x hx
  by_cases haX : a ≤ ‖x‖
  · have hn : 0 < ‖x‖ := ha.trans_le haX
    have hZ : Z*coulombKernel x ≤ |Z|/a := by
      unfold coulombKernel
      calc
        Z*‖x‖⁻¹ ≤ |Z| *‖x‖⁻¹ := mul_le_mul_of_nonneg_right (le_abs_self _) (inv_nonneg.mpr hn.le)
        _ ≤ |Z| *a⁻¹ := mul_le_mul_of_nonneg_left (inv_anti₀ ha haX) (abs_nonneg _)
        _ = |Z|/a := by rw [div_eq_mul_inv]
    have h := tfReaction_monotone (show Z*coulombKernel x+f x ≤ |Z|/a+D by
      have H : f x ≤ D := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hD x hx)
      linarith)
    simpa [cutoffReaction, haX, abs_of_nonneg (tfReaction_nonneg _)] using h
  · simpa [cutoffReaction, haX] using tfReaction_nonneg (|Z|/a+D)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma joint_compact_test_integrable {F : Ω → Position → ℝ}
    (hm : Measurable (Function.uncurry F))
    (hb : ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R → |F o x| ≤ C)
    {φ : Position → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Integrable (fun z : Ω × Position => F z.1 z.2*φ z.2) (μ.prod volume) := by
  obtain ⟨R,hR⟩ := hc.isBounded.subset_closedBall (0:Position)
  obtain ⟨C,hC⟩ := hb R
  have hi : Integrable (fun z : Ω × Position => C*‖φ z.2‖) (μ.prod volume) :=
    ((hφ.integrable_of_hasCompactSupport hc).norm.const_mul C).comp_snd μ
  apply hi.mono' (hm.mul (hφ.measurable.comp measurable_snd)).aestronglyMeasurable
  filter_upwards [] with z
  change ‖F z.1 z.2*φ z.2‖ ≤ C*‖φ z.2‖
  rw [norm_mul,Real.norm_eq_abs (F z.1 z.2)]
  by_cases hz : z.2 ∈ tsupport φ
  · exact mul_le_mul_of_nonneg_right (hC z.1 z.2 (hR hz)) (norm_nonneg _)
  · simp [image_eq_zero_of_notMem_tsupport hz]

lemma integral_average_test {F : Ω → Position → ℝ}
    (hm : Measurable (Function.uncurry F))
    (hb : ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R → |F o x| ≤ C)
    {φ : Position → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    (∫ x, (∫ o, F o x ∂μ)*φ x)=(∫ o, (∫ x, F o x*φ x) ∂μ) := by
  simp_rw [←integral_mul_const]
  exact (integral_integral_swap (joint_compact_test_integrable hm hb hφ hc)).symm

theorem WeakLaplacianGE.average {F Q : Ω → Position → ℝ} {U : Set Position}
    (hF : Measurable (Function.uncurry F)) (hQ : Measurable (Function.uncurry Q))
    (hbF : ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R → |F o x| ≤ C)
    (hbQ : ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R → |Q o x| ≤ C)
    (hw : ∀ᵐ o ∂μ, WeakLaplacianGE (F o) U (Q o)) :
    WeakLaplacianGE (fun x => ∫ o, F o x ∂μ) U (fun x => ∫ o, Q o x ∂μ) := by
  intro φ hφ hc ht hp
  rw [integral_average_test hQ hbQ hφ.continuous hc,
    integral_average_test hF hbF (contDiff_coordinateLaplacian hφ).continuous
      (hasCompactSupport_coordinateLaplacian hc)]
  apply integral_mono_ae
    (joint_compact_test_integrable hQ hbQ hφ.continuous hc).integral_prod_left
    (joint_compact_test_integrable hF hbF (contDiff_coordinateLaplacian hφ).continuous
      (hasCompactSupport_coordinateLaplacian hc)).integral_prod_left
  filter_upwards [hw] with o ho
  exact ho φ hφ hc ht hp

theorem tfReaction_integral_le {f : Ω → ℝ} (hf : Integrable f μ)
    (hr : Integrable (fun o => (max (f o) 0)^(3/2:ℝ)) μ) :
    tfReaction (∫ o, f o ∂μ) ≤ ∫ o, tfReaction (f o) ∂μ := by
  have hpos : Integrable (fun o => max (f o) 0) μ := hf.sup (integrable_const 0)
  have hm : max (∫ o, f o ∂μ) 0 ≤ ∫ o, max (f o) 0 ∂μ := max_le
    (integral_mono hf hpos (fun o => le_max_left _ _))
    (integral_nonneg (fun o => le_max_right _ _))
  have hJ := (convexOn_rpow (by norm_num : (1:ℝ) ≤ 3/2)).map_integral_le
    (Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 3/2)).continuousOn isClosed_Ici
    (Eventually.of_forall (fun o => (show max (f o) 0 ∈ Ici (0:ℝ) from (show 0 ≤ max (f o) 0 from le_max_right _ _)))) hpos hr
  unfold tfReaction
  rw [integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ (by have := kTF_pos; positivity)
  exact (Real.rpow_le_rpow (le_max_right _ _) hm (by norm_num)).trans hJ

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

lemma nuclear_offset_test_identity {f φ : Position → ℝ} (hf : Continuous f)
    (Z : ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x, (Z*coulombKernel x+f x)*coordinateLaplacian φ x)=
      -(4*Real.pi*Z*φ 0)+(∫ x, f x*coordinateLaplacian φ x) := by
  have hL := (contDiff_coordinateLaplacian hφ).continuous
  have hLc := hasCompactSupport_coordinateLaplacian hc
  have hiK : Integrable (fun x => coulombKernel x*coordinateLaplacian φ x) := by
    simpa only [smul_eq_mul] using
      locallyIntegrable_coulombKernel.integrable_smul_right_of_hasCompactSupport hL hLc
  have hiF := integrable_mul_compact_of_continuousAt (fun x _ => hf.continuousAt) hL hLc
  simp_rw [add_mul]
  rw [integral_add (by simpa only [mul_assoc] using hiK.const_mul Z) hiF]
  simp_rw [mul_assoc Z]
  rw [integral_const_mul,integral_coulombKernel_laplacian hφ hc]
  ring

theorem weakNuclearSubsolution_offset_iff {f q : Position → ℝ} {Z : ℝ} {U : Set Position}
    (hf : Continuous f) :
    WeakNuclearSubsolution (fun x => Z*coulombKernel x+f x) Z U q ↔ WeakLaplacianGE f U q := by
  constructor <;> intro h φ hφ hc ht hp
  · have H := h φ hφ hc ht hp
    rw [nuclear_offset_test_identity hf Z hφ hc] at H
    linarith
  · rw [nuclear_offset_test_identity hf Z hφ hc]
    linarith [h φ hφ hc ht hp]

theorem WeakNuclearSubsolution.max_reaction {f g b : Position → ℝ} {Z : ℝ}
    {F : Position → ℝ → ℝ} {U : Set Position}
    (hU : IsOpen U) (hf : Continuous f) (hg : Continuous g)
    (hq : LocallyIntegrable (fun x => b x+F x (Z*coulombKernel x+f x)) volume)
    (hr : LocallyIntegrable (fun x => b x+F x (Z*coulombKernel x+g x)) volume)
    (hbq : ∀ R : ℝ, ∃ C : ℝ, ∀ x ∈ Metric.closedBall 0 R,
      |b x+F x (Z*coulombKernel x+f x)| ≤ C)
    (hbr : ∀ R : ℝ, ∃ C : ℝ, ∀ x ∈ Metric.closedBall 0 R,
      |b x+F x (Z*coulombKernel x+g x)| ≤ C)
    (hwf : WeakNuclearSubsolution (fun x => Z*coulombKernel x+f x) Z U
      (fun x => b x+F x (Z*coulombKernel x+f x)))
    (hwg : WeakNuclearSubsolution (fun x => Z*coulombKernel x+g x) Z U
      (fun x => b x+F x (Z*coulombKernel x+g x))) :
    WeakNuclearSubsolution (fun x => Z*coulombKernel x+max (f x) (g x)) Z U
      (fun x => b x+F x (Z*coulombKernel x+max (f x) (g x))) := by
  apply (weakNuclearSubsolution_offset_iff (hf.max hg)).2
  exact WeakLaplacianGE.max_reaction (F := fun x t => F x (Z*coulombKernel x+t))
    hU hf hg hq hr hbq hbr
    ((weakNuclearSubsolution_offset_iff (Z:=Z) hf).1 hwf)
    ((weakNuclearSubsolution_offset_iff (Z:=Z) hg).1 hwg)

theorem WeakNuclearSubsolution.average {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f q : Ω → Position → ℝ} {Z : ℝ} {U : Set Position}
    (hf : ∀ o, Continuous (f o))
    (hcf : Continuous (fun x => ∫ o, f o x ∂μ))
    (hmf : Measurable (Function.uncurry f)) (hmq : Measurable (Function.uncurry q))
    (hbf : ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R → |f o x| ≤ C)
    (hbq : ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R → |q o x| ≤ C)
    (hw : ∀ᵐ o ∂μ, WeakNuclearSubsolution (fun x => Z*coulombKernel x+f o x) Z U (q o)) :
    WeakNuclearSubsolution (fun x => Z*coulombKernel x+∫ o, f o x ∂μ) Z U
      (fun x => ∫ o, q o x ∂μ) := by
  apply (weakNuclearSubsolution_offset_iff hcf).2
  apply WeakLaplacianGE.average hmf hmq hbf hbq
  filter_upwards [hw] with o ho
  exact (weakNuclearSubsolution_offset_iff (hf o)).1 ho

end NeutralAtom

end

end OAI
