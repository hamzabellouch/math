import OAI.Geometry.SurfaceImmersion.Correction.SmoothingDerivatives
import Mathlib.Topology.UniformSpace.HeineCantor

namespace OAI

/-! Uniform approximation of C1 coordinate maps by the existing smooth kernel. -/
noncomputable section
open scoped ContDiff Convolution Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory Set Filter ContinuousLinearMap
open JetPolynomial (Base)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma fderiv_smooth_C1 (r : ℕ) {s : ℝ} (hs : 0 < s) {f : Base → E}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (x : Base) :
    fderiv ℝ (smooth r s f) x = smooth r s (fderiv ℝ f) x := by
  let L : ℝ →L[ℝ] E →L[ℝ] E := lsmul ℝ ℝ
  have hk : LocallyIntegrable (dilate (kernel r) s) volume :=
    (((smooth_dilate (kernel_smooth r) s).continuous).integrable_of_hasCompactSupport
      (compact_dilate (kernel_compact r) hs.ne')).locallyIntegrable
  have h := hfc.hasFDerivAt_convolution_right L hk hf x
  have heq : ((dilate (kernel r) s) ⋆[L.precompR Base, volume] fderiv ℝ f) x =
      smooth r s (fderiv ℝ f) x := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun y => by ext v; rfl)
  exact h.fderiv.trans heq

/-- Uniform continuity suffices for uniform convergence of the signed
finite-moment kernel. Positivity of the kernel is not required. -/
theorem smooth_uniform_approximation (r : ℕ) {f : Base → E}
    (hf : UniformContinuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 0 < s → s < η →
      ∀ x : Base, ‖smooth r s f x-f x‖ ≤ ε := by
  let C : ℝ := ∫ y, ‖kernel r y‖
  have hC : 0 ≤ C := integral_nonneg (fun _ => norm_nonneg _)
  have ha : 0 < ε/(C+1) := div_pos hε (by linarith)
  obtain ⟨δ,hδ,hδf⟩ := Metric.uniformContinuous_iff.mp hf (ε/(C+1)) ha
  obtain ⟨R,hR,hRK⟩ := (kernel_compact r).isCompact.isBounded.exists_pos_norm_le
  refine ⟨δ/(R+1),div_pos hδ (by linarith),?_⟩
  intro s hs hsη x
  let k := dilate (kernel r) s
  have hk : HasCompactSupport k := compact_dilate (kernel_compact r) hs.ne'
  have hkc : Continuous k := (smooth_dilate (kernel_smooth r) s).continuous
  have hki : Integrable k volume := hkc.integrable_of_hasCompactSupport hk
  have hloc : LocallyIntegrable f volume := hf.continuous.locallyIntegrable
  have hif := hk.convolutionExists_left (lsmul ℝ ℝ) hkc hloc x
  have hif' : Integrable (fun y => k y • f (x-y)) volume := hif
  have heq : smooth r s f x-f x = ∫ y, k y • (f (x-y)-f x) := by
    symm
    simp_rw [smul_sub]
    rw [integral_sub hif' (hki.smul_const (f x)),integral_smul_const]
    change smooth r s f x-(∫ y, dilate (kernel r) s y) • f x = _
    rw [mass_dilate _ hs,kernel_mass,one_smul]
  have hbound (y : Base) : ‖k y • (f (x-y)-f x)‖ ≤ ‖k y‖*(ε/(C+1)) := by
    by_cases hy : k y = 0
    · simp [hy]
    have hyn : kernel r (s⁻¹ • y) ≠ 0 := (mul_ne_zero_iff.mp hy).2
    have hyR := hRK (s⁻¹ • y) (subset_tsupport _ hyn)
    have hn : ‖y‖ ≤ R*s := by
      rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hs] at hyR
      have hh : ‖y‖/s ≤ R := by simpa only [div_eq_mul_inv,mul_comm] using hyR
      exact (div_le_iff₀ hs).mp hh
    have hsR : R*s < δ := by
      have hh := (lt_div_iff₀ (show 0 < R+1 by linarith)).mp hsη
      nlinarith
    have hd : dist (x-y) x < δ := by
      simpa only [dist_eq_norm,sub_sub_cancel_left,norm_neg] using hn.trans_lt hsR
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (le_of_lt (by
      simpa only [dist_eq_norm] using hδf hd)) (norm_nonneg _)
  rw [heq]
  calc
    ‖∫ y, k y • (f (x-y)-f x)‖ ≤ ∫ y, ‖k y‖*(ε/(C+1)) :=
      norm_integral_le_of_norm_le (hki.norm.mul_const _) (Eventually.of_forall hbound)
    _ = C*(ε/(C+1)) := by rw [integral_mul_const,norm_mass_dilate _ hs]
    _ ≤ ε := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (show 0 < C+1 by linarith)).mpr
      nlinarith

/-- Compactly supported C1 maps have smooth approximants converging uniformly
both as maps and in their first derivatives. -/
theorem smooth_C1_approximation (r : ℕ) {f : Base → E}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 0 < s → s < η →
      ContDiff ℝ ∞ (smooth r s f) ∧
      ∀ x, ‖smooth r s f x-f x‖ ≤ ε ∧
        ‖fderiv ℝ (smooth r s f) x-fderiv ℝ f x‖ ≤ ε := by
  have hu := hfc.uniformContinuous_of_continuous hf.continuous
  have hd : UniformContinuous (fderiv ℝ f) :=
    (hfc.fderiv ℝ).uniformContinuous_of_continuous (hf.continuous_fderiv one_ne_zero)
  obtain ⟨η₁,hη₁,h₁⟩ := smooth_uniform_approximation r hu hε
  obtain ⟨η₂,hη₂,h₂⟩ := smooth_uniform_approximation r hd hε
  refine ⟨min η₁ η₂,lt_min hη₁ hη₂,?_⟩
  intro s hs hsη
  refine ⟨smooth_smooth r hs hf.continuous.locallyIntegrable,?_⟩
  intro x
  refine ⟨h₁ s hs (hsη.trans_le (min_le_left _ _)) x,?_⟩
  rw [fderiv_smooth_C1 r hs hf hfc]
  exact h₂ s hs (hsη.trans_le (min_le_right _ _)) x

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
