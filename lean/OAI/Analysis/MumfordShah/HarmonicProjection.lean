import Mathlib
import OAI.Analysis.MumfordShah.Variations
import OAI.Analysis.MumfordShah.WeakHarmonic

namespace OAI

/-! MumfordShah harmonic projection. -/

noncomputable section
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
namespace MumfordShah
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff
open Set MeasureTheory Topology InnerProductSpace
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology Filter
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology Filter
open scoped ContDiff
open Set MeasureTheory Topology InnerProductSpace
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff
open Filter
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set Metric Topology InnerProductSpace Complex MeasureTheory
open scoped ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal ContDiff

lemma locallyIntegrable_of_local_sobolev {φ : ℂ → ℝ} {w : ℂ → ℂ}
    (hφ : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → SobolevOn φ w S) :
    LocallyIntegrable φ volume := by
  intro x
  refine ⟨ball x 1, ball_mem_nhds x zero_lt_one, ?_⟩
  let : IsFiniteMeasure (volume.restrict (ball x 1)) :=
    isFiniteMeasure_restrict.mpr (measure_ball_lt_top.ne)
  exact (hφ (ball x 1) isOpen_ball isBounded_ball).1.integrable (by norm_num)

lemma weak_gradient_global_integral {φ : ℂ → ℝ} {w : ℂ → ℂ}
    (hφ : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → SobolevOn φ w S)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (a : ℂ) :
    (∫ x : ℂ, φ x * fderiv ℝ ψ x a) = -(∫ x : ℂ, inner ℝ (w x) a * ψ x) := by
  obtain ⟨R, hR⟩ := hc.isBounded.subset_ball (0 : ℂ)
  have h := (hφ (ball 0 R) isOpen_ball isBounded_ball).2.2 ψ hψ hc hR a
  rwa [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [fderiv_of_notMem_tsupport ℝ (fun ht => hx (hR ht))]; simp),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hR ht)), mul_zero])] at h

lemma complex_real_inner_formula (z w : ℂ) :
    inner ℝ z w = z.re * w.re + z.im * w.im := by
  rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply]
  change (w * star z).re = _
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

lemma inner_gradient_components (w : ℂ) (ψ : ℂ → ℝ) (x : ℂ) :
    inner ℝ w (gradient ψ x) =
      inner ℝ w 1 * fderiv ℝ ψ x 1 +
      inner ℝ w Complex.I * fderiv ℝ ψ x Complex.I := by
  rw [real_inner_comm (gradient ψ x) w, inner_gradient_left]
  have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
    simp
  conv_lhs => rw [hw, map_add, map_smul, map_smul]
  simp

lemma integrable_inner_memLp {f g : ℂ → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun x => inner ℝ (f x) (g x)) volume := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx,hy]

lemma integrable_local_mul_test {φ ψ : ℂ → ℝ} (hφ : LocallyIntegrable φ volume)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun x => φ x * ψ x) volume :=
  hφ.integrable_smul_right_of_hasCompactSupport hψ hc

lemma integral_laplacian_weak_gradient {φ : ℂ → ℝ} {w : PlaneL2}
    (hφ : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → SobolevOn φ w S)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    (∫ x : ℂ, φ x * Δ ψ x) = -(∫ x : ℂ, inner ℝ (w x) (gradient ψ x)) := by
  have hli := locallyIntegrable_of_local_sobolev hφ
  have hi (a : ℂ) : Integrable (fun x => φ x * fderiv ℝ (fun y => fderiv ℝ ψ y a) x a) volume :=
    integrable_local_mul_test hli (smooth_directional (smooth_directional hψ a) a).continuous
      (compact_directional (compact_directional hc a) a)
  have hj (a : ℂ) : Integrable (fun x => inner ℝ (w x) a * fderiv ℝ ψ x a) volume := by
    have hh := integrable_inner_memLp (Lp.memLp w)
      (memLp_test_vector (smooth_directional hψ a).continuous (compact_directional hc a) a)
    simpa only [inner_smul_right, mul_comm] using hh
  have hpoint (x : ℂ) : Δ ψ x =
      fderiv ℝ (fun y => fderiv ℝ ψ y 1) x 1 +
      fderiv ℝ (fun y => fderiv ℝ ψ y Complex.I) x Complex.I := by
    simp only [laplacian_eq_iteratedFDeriv_complexPlane,iteratedFDeriv_two_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, fderiv_directional hψ]
  simp_rw [hpoint, mul_add, inner_gradient_components]
  rw [integral_add (hi 1) (hi Complex.I), integral_add (hj 1) (hj Complex.I),
    weak_gradient_global_integral hφ (smooth_directional hψ 1) (compact_directional hc 1),
    weak_gradient_global_integral hφ (smooth_directional hψ Complex.I) (compact_directional hc Complex.I)]
  ring

lemma projection_test_identity (e : PlaneL2) {ψ : ℂ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    (∫ x : ℂ, inner ℝ (compactGradientProjection e x) (gradient ψ x)) =
      ∫ x : ℂ, inner ℝ (e x) (gradient ψ x) := by
  have h := compactJumpField_divergence_free e hψ hc
  have he : (∫ x : ℂ, inner ℝ (compactJumpField e x) (gradient ψ x)) =
      (∫ x : ℂ, inner ℝ (e x) (gradient ψ x)) -
      ∫ x : ℂ, inner ℝ (compactGradientProjection e x) (gradient ψ x) := by
    rw [← integral_sub (integrable_inner_memLp (Lp.memLp e) (memLp_gradient_of_test hψ hc))
      (integrable_inner_memLp (Lp.memLp _) (memLp_gradient_of_test hψ hc))]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub e (compactGradientProjection e)] with x hx
    change (e - compactGradientProjection e) x = e x - compactGradientProjection e x at hx
    simp only [compactJumpField, hx, inner_sub_left]
  rw [he] at h
  linarith

lemma SobolevOn.congr_ae {φ v : ℂ → ℝ} {w : ℂ → ℂ} {S : Set ℂ}
    (hφ : SobolevOn φ w S) (hv : v =ᵐ[volume] φ) : SobolevOn v w S := by
  have he : v =ᵐ[volume.restrict S] φ := ae_restrict_of_ae hv
  refine ⟨hφ.1.ae_eq he.symm, hφ.2.1, ?_⟩
  intro ψ hψ hc hs a
  rw [show (∫ x in S, v x * fderiv ℝ ψ x a) = ∫ x in S, φ x * fderiv ℝ ψ x a from
    integral_congr_ae (by filter_upwards [he] with x hx; rw [hx])]
  exact hφ.2.2 ψ hψ hc hs a

lemma projected_potential_weak_harmonic {e : PlaneL2} {φ : ℂ → ℝ} {O : Set ℂ}
    (hφ : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S →
      SobolevOn φ (compactGradientProjection e) S)
    (he : ∀ᵐ x ∂volume, x ∈ O → e x = 0) : WeakHarmonicOn φ O := by
  intro ψ hψ hc hs
  rw [integral_laplacian_weak_gradient hφ hψ hc, projection_test_identity e hψ hc]
  have hz : (∫ x : ℂ, inner ℝ (e x) (gradient ψ x)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [he] with x hx
    by_cases hxo : x ∈ O
    · rw [hx hxo]; simp
    · have hd := fderiv_of_notMem_tsupport ℝ (f := ψ) (x := x) (fun ht => hxo (hs ht))
      simp [gradient, hd]
  rw [hz, neg_zero]

theorem projection_has_harmonic_local_potential (e : PlaneL2) {O : Set ℂ}
    (hO : IsOpen O) (he : ∀ᵐ x ∂volume, x ∈ O → e x = 0) :
    ∃ φ : ℂ → ℝ,
      (∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S →
        SobolevOn φ (compactGradientProjection e) S) ∧
      ContDiffOn ℝ ∞ φ O ∧ HarmonicOnNhd φ O := by
  obtain ⟨φ, hφ⟩ := gradient_closure_has_local_potential
    (compactGradientClosure.starProjection_apply_mem e)
  obtain ⟨v, hv, hs, hh⟩ := weak_harmonic_regular
    (locallyIntegrable_of_local_sobolev hφ) hO (projected_potential_weak_harmonic hφ he)
  exact ⟨v, fun S hS hB => (hφ S hS hB).congr_ae hv, hs, hh⟩

lemma local_smooth_weak_derivative_ae {u : ℂ → ℝ} {w : ℂ → ℂ} {O : Set ℂ}
    (hu : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → SobolevOn u w S)
    (hw : MemLp w 2 volume) (hO : IsOpen O) (hs : ContDiffOn ℝ ∞ u O) (a : ℂ) :
    ∀ᵐ x ∂volume, x ∈ O → fderiv ℝ u x a = inner ℝ (w x) a := by
  have hd : ContinuousOn (fun x => fderiv ℝ u x a) O :=
    (hs.continuousOn_fderiv_of_isOpen hO (by norm_num)).clm_apply continuousOn_const
  have hli := hd.locallyIntegrableOn (μ := volume) hO.measurableSet
  have hlw := ((hw.inner_const (𝕜 := ℝ) a).locallyIntegrable (by norm_num)).locallyIntegrableOn O
  have hzero := hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hli.sub hlw) ?_
  · filter_upwards [hzero] with x hx
    exact fun ho => sub_eq_zero.mp (hx ho)
  intro ψ hψ hc ht
  have hψd : Continuous (fun x => fderiv ℝ ψ x a) :=
    (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hψdc : HasCompactSupport (fun x => fderiv ℝ ψ x a) :=
    hc.fderiv_apply ℝ a
  have hψdt : tsupport (fun x => fderiv ℝ ψ x a) ⊆ O := by
    exact (tsupport_fderiv_apply_subset ℝ a).trans ht
  have hip := integrable_mul_compact_of_continuousOn hd hψ.continuous hc ht
  have hiw : Integrable (fun x => inner ℝ (w x) a * ψ x) volume :=
    integrable_local_mul_test ((hw.inner_const (𝕜 := ℝ) a).locallyIntegrable (by norm_num))
      hψ.continuous hc
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) hip (integrable_mul_compact_of_continuousOn hs.continuousOn hψd hψdc hψdt)
    (integrable_mul_compact_of_continuousOn hs.continuousOn hψ.continuous hc ht)
    (fun x hx => ((hs x (ht hx)).contDiffAt (hO.mem_nhds (ht hx))).differentiableAt (by norm_num))
    (fun x _ => hψ.differentiable (by norm_num) x)
  have hiweak := weak_gradient_global_integral hu hψ hc a
  simp only [smul_eq_mul, Pi.sub_apply, mul_sub]
  rw [integral_sub (by simpa only [mul_comm] using hip) (by simpa only [mul_comm] using hiw)]
  simp_rw [mul_comm (ψ _)]
  linarith

lemma local_smooth_weak_gradient_ae {u : ℂ → ℝ} {w : ℂ → ℂ} {O : Set ℂ}
    (hu : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → SobolevOn u w S)
    (hw : MemLp w 2 volume) (hO : IsOpen O) (hs : ContDiffOn ℝ ∞ u O) :
    ∀ᵐ x ∂volume, x ∈ O → gradient u x = w x := by
  filter_upwards [local_smooth_weak_derivative_ae hu hw hO hs 1,
    local_smooth_weak_derivative_ae hu hw hO hs Complex.I] with x hx hy
  intro hxo
  have hx' := hx hxo
  have hy' := hy hxo
  rw [← inner_gradient_left] at hx' hy'
  simp only [complex_real_inner_formula, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_add, add_zero] at hx' hy'
  exact Complex.ext hx' hy'

theorem projection_has_classical_harmonic_potential (e : PlaneL2) {O : Set ℂ}
    (hO : IsOpen O) (he : ∀ᵐ x ∂volume, x ∈ O → e x = 0) :
    ∃ φ : ℂ → ℝ,
      (∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S →
        SobolevOn φ (compactGradientProjection e) S) ∧
      ContDiffOn ℝ ∞ φ O ∧ HarmonicOnNhd φ O ∧
      (∀ᵐ x ∂volume, x ∈ O → gradient φ x = compactGradientProjection e x) := by
  obtain ⟨φ,hφ,hs,hh⟩ := projection_has_harmonic_local_potential e hO he
  exact ⟨φ,hφ,hs,hh,local_smooth_weak_gradient_ae hφ (Lp.memLp _) hO hs⟩

end MumfordShah
end

end OAI
