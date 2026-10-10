import Mathlib
import OAI.Analysis.MumfordShah.ExteriorPotential

namespace OAI

/-! MumfordShah decomposition. -/

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

open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap

open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff

instance decompositionCompleteSpaceCompactGradientClosure : CompleteSpace compactGradientClosure := by
  unfold compactGradientClosure
  infer_instance

lemma weak_gradient_integral_on {u : ℂ → ℝ} {m : ℂ → ℂ} {U : Set ℂ}
    (hu : SobolevOn u m U) {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (ht : tsupport ψ ⊆ U) (a : ℂ) :
    (∫ x : ℂ, u x * fderiv ℝ ψ x a) = -(∫ x : ℂ, inner ℝ (m x) a * ψ x) := by
  have h := hu.2.2 ψ hψ hc ht a
  rwa [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [fderiv_of_notMem_tsupport ℝ (fun hn => hx (ht hn))]; simp),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport (fun hn => hx (ht hn)), mul_zero])] at h

lemma laplacian_test_zero_off_support {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {x : ℂ} (hx : x ∉ tsupport ψ) : Δ ψ x = 0 := by
  have hz (a : ℂ) : fderiv ℝ (fun y => fderiv ℝ ψ y a) x = 0 :=
    fderiv_of_notMem_tsupport ℝ (fun hn => hx (tsupport_fderiv_apply_subset ℝ a hn))
  have hpoint : Δ ψ x =
      fderiv ℝ (fun y => fderiv ℝ ψ y 1) x 1 +
      fderiv ℝ (fun y => fderiv ℝ ψ y Complex.I) x Complex.I := by
    simp only [laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_two_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, fderiv_directional hψ]
  simp [hpoint, hz]

lemma local_sobolev_laplacian_identity {u : ℂ → ℝ} {m : ℂ → ℂ} {U : Set ℂ}
    (hu : SobolevOn u m U) {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (ht : tsupport ψ ⊆ U) :
    (∫ x : ℂ, u x * Δ ψ x) = -(∫ x : ℂ, inner ℝ (m x) (gradient ψ x)) := by
  have hi (a : ℂ) : Integrable (fun x => u x * fderiv ℝ (fun y => fderiv ℝ ψ y a) x a)
      (volume.restrict U) :=
    hu.1.integrable_mul (q := 2)
      ((smooth_directional (smooth_directional hψ a) a).continuous.memLp_of_hasCompactSupport
        (compact_directional (compact_directional hc a) a))
  have hj (a : ℂ) : Integrable (fun x => inner ℝ (m x) a * fderiv ℝ ψ x a)
      (volume.restrict U) :=
    (hu.2.1.inner_const (𝕜 := ℝ) a).integrable_mul (q := 2)
      ((smooth_directional hψ a).continuous.memLp_of_hasCompactSupport (compact_directional hc a))
  have hpoint (x : ℂ) : Δ ψ x =
      fderiv ℝ (fun y => fderiv ℝ ψ y 1) x 1 +
      fderiv ℝ (fun y => fderiv ℝ ψ y Complex.I) x Complex.I := by
    simp only [laplacian_eq_iteratedFDeriv_complexPlane,iteratedFDeriv_two_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, fderiv_directional hψ]
  have hh : (∫ x in U, u x * Δ ψ x) = -(∫ x in U, inner ℝ (m x) (gradient ψ x)) := by
    simp_rw [hpoint, mul_add, inner_gradient_components]
    rw [integral_add (hi 1) (hi Complex.I), integral_add (hj 1) (hj Complex.I),
      hu.2.2 _ (smooth_directional hψ 1) (compact_directional hc 1)
        ((tsupport_fderiv_apply_subset ℝ 1).trans ht) 1,
      hu.2.2 _ (smooth_directional hψ Complex.I) (compact_directional hc Complex.I)
        ((tsupport_fderiv_apply_subset ℝ Complex.I).trans ht) Complex.I]
    ring
  rwa [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [laplacian_test_zero_off_support hψ (fun hn => hx (ht hn)), mul_zero]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    simp [gradient, fderiv_of_notMem_tsupport ℝ (fun hn => hx (ht hn))])] at hh

lemma local_smooth_weak_derivative_ae_on {u : ℂ → ℝ} {w : ℂ → ℂ} {O : Set ℂ}
    (hu : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → SobolevOn u w (S ∩ O))
    (hw : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → MemLp w 2 (volume.restrict S))
    (hO : IsOpen O) (hs : ContDiffOn ℝ ∞ u O) (a : ℂ) :
    ∀ᵐ x ∂volume, x ∈ O → fderiv ℝ u x a = inner ℝ (w x) a := by
  have hwL : LocallyIntegrable (fun x => inner ℝ (w x) a) volume := by
    intro x
    refine ⟨ball x 1, ball_mem_nhds x zero_lt_one, ?_⟩
    have : IsFiniteMeasure (volume.restrict (ball x 1)) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    exact ((hw _ isOpen_ball isBounded_ball).inner_const (𝕜 := ℝ) a).integrable (by norm_num)
  have hd : ContinuousOn (fun x => fderiv ℝ u x a) O :=
    (hs.continuousOn_fderiv_of_isOpen hO (by norm_num)).clm_apply continuousOn_const
  have hli := hd.locallyIntegrableOn (μ := volume) hO.measurableSet
  have hzero := hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hli.sub (hwL.locallyIntegrableOn O)) ?_
  · filter_upwards [hzero] with x hx
    exact fun ho => sub_eq_zero.mp (hx ho)
  intro ψ hψ hc ht
  have hψd : Continuous (fun x => fderiv ℝ ψ x a) :=
    (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hψdc : HasCompactSupport (fun x => fderiv ℝ ψ x a) := hc.fderiv_apply ℝ a
  have hψdt : tsupport (fun x => fderiv ℝ ψ x a) ⊆ O := (tsupport_fderiv_apply_subset ℝ a).trans ht
  have hip := integrable_mul_compact_of_continuousOn hd hψ.continuous hc ht
  have hiw : Integrable (fun x => inner ℝ (w x) a * ψ x) volume :=
    hwL.integrable_smul_right_of_hasCompactSupport hψ.continuous hc
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) hip (integrable_mul_compact_of_continuousOn hs.continuousOn hψd hψdc hψdt)
    (integrable_mul_compact_of_continuousOn hs.continuousOn hψ.continuous hc ht)
    (fun x hx => ((hs x (ht hx)).contDiffAt (hO.mem_nhds (ht hx))).differentiableAt (by norm_num))
    (fun x _ => hψ.differentiable (by norm_num) x)
  obtain ⟨R, hR⟩ := hc.isBounded.subset_ball (0 : ℂ)
  have hiweak := weak_gradient_integral_on (hu _ isOpen_ball isBounded_ball) hψ hc (subset_inter hR ht) a
  simp only [smul_eq_mul, Pi.sub_apply, mul_sub]
  rw [integral_sub (by simpa only [mul_comm] using hip) (by simpa only [mul_comm] using hiw)]
  simp_rw [mul_comm (ψ _)]
  linarith
lemma local_smooth_weak_gradient_ae_on {u : ℂ → ℝ} {w : ℂ → ℂ} {O : Set ℂ}
    (hu : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → SobolevOn u w (S ∩ O))
    (hw : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → MemLp w 2 (volume.restrict S)) (hO : IsOpen O) (hs : ContDiffOn ℝ ∞ u O) :
    ∀ᵐ x ∂volume, x ∈ O → gradient u x = w x := by
  filter_upwards [local_smooth_weak_derivative_ae_on hu hw hO hs 1,
    local_smooth_weak_derivative_ae_on hu hw hO hs Complex.I] with x hx hy
  intro hxo
  have hx' := hx hxo
  have hy' := hy hxo
  rw [← inner_gradient_left] at hx' hy'
  simp only [complex_real_inner_formula, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_add, add_zero] at hx' hy'
  exact Complex.ext hx' hy'

theorem local_sobolev_divergence_free_regular {u : ℂ → ℝ} {w : ℂ → ℂ} {O : Set ℂ}
    (hO : IsOpen O)
    (hu : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → SobolevOn u w (S ∩ O))
    (hw : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → MemLp w 2 (volume.restrict S))
    (huli : LocallyIntegrable u volume)
    (hdiv : ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ O →
      (∫ x : ℂ, inner ℝ (w x) (gradient ψ x)) = 0) :
    ∃ f : ℂ → ℝ, f =ᵐ[volume] u ∧ ContDiffOn ℝ ∞ f O ∧ HarmonicOnNhd f O ∧
      (∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → SobolevOn f w (S ∩ O)) ∧
      (∀ᵐ x ∂volume, x ∈ O → gradient f x = w x) := by
  have hh : WeakHarmonicOn u O := by
    intro ψ hψ hc ht
    obtain ⟨R, hR⟩ := hc.isBounded.subset_ball (0 : ℂ)
    rw [local_sobolev_laplacian_identity (hu _ isOpen_ball isBounded_ball) hψ hc
      (subset_inter hR ht), hdiv ψ hψ hc ht, neg_zero]
  obtain ⟨f, heq, hfs, hfh⟩ := weak_harmonic_regular huli hO hh
  have hf : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → SobolevOn f w (S ∩ O) :=
    fun S hS hB => (hu S hS hB).congr_ae heq
  exact ⟨f, heq, hfs, hfh, hf, local_smooth_weak_gradient_ae_on hf hw hO hfs⟩

theorem minimizer_harmonic_decomposition {v : Pair} (hv : GlobalAbsoluteMinimizer v)
    {A B : Set ℂ} (hA : IsCompact A) (hB : IsClosed B)
    (hAB : Disjoint A B) (hH : v.K = A ∪ B) :
    ∃ h : ℂ → ℝ, ∃ e : ℂ → ℂ, ∃ he : MemLp e 2 volume,
      ∃ φ F f : ℂ → ℝ, ∃ R : ℝ,
      SobolevOn h e Aᶜ ∧ IsCompact (essentialSupport h) ∧ essentialSupport h ⊆ Bᶜ ∧
      0 < R ∧
      (∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S →
        SobolevOn φ (compactGradientProjection (he.toLp e)) S) ∧
      F =ᵐ[volume] h - φ ∧
      (∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S →
        SobolevOn F (compactJumpField (he.toLp e)) (S \ A)) ∧
      ContDiffOn ℝ ∞ F {z | R < ‖z‖} ∧ HarmonicOnNhd F {z | R < ‖z‖} ∧
      (∀ᵐ x ∂volume, R < ‖x‖ → gradient F x = compactJumpField (he.toLp e) x) ∧
      Tendsto φ (cocompact ℂ) (𝓝 0) ∧
      (∀ k : ℕ, ∃ C : ℝ, ∀ᶠ z in cocompact ℂ,
        ‖iteratedFDeriv ℝ k F z‖ ≤ C * ‖z‖⁻¹ ^ (k+1)) ∧
      ContDiffOn ℝ ∞ f Bᶜ ∧ HarmonicOnNhd f Bᶜ ∧
      (∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S →
        SobolevOn f (fun x => v.grad x - compactJumpField (he.toLp e) x) (S \ B)) ∧
      (∀ᵐ x ∂volume, x ∉ B → gradient f x = v.grad x - compactJumpField (he.toLp e) x) ∧
      v.u =ᵐ[volume] f + F ∧
      (∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        (∫ x : ℂ, inner ℝ (v.grad x - compactJumpField (he.toLp e) x) (gradient ψ x)) = 0) := by
  have hH0 : volume v.K = 0 := volume_eq_zero_of_locally_finite_length hv.1.2.2.1
  have hA0 : volume A = 0 := measure_mono_null (by rw [hH]; exact subset_union_left) hH0
  have hB0 : volume B = 0 := measure_mono_null (by rw [hH]; exact subset_union_right) hH0
  obtain ⟨χ,hχ,hχc,hχt,hχ1,hχr⟩ := compact_smooth_cutoff hA hB.isOpen_compl
    (Set.disjoint_left.mp hAB)
  let h := fun x => χ x * v.u x
  let e := fun x => χ x • v.grad x + v.u x • gradient χ x
  obtain ⟨hhe,hhc,hk⟩ := cutoff_sobolev_decomposition hv.1 hA hB hH hχ hχc hχt hχ1
  have hht : essentialSupport h ⊆ Bᶜ :=
    (essentialSupport_subset_tsupport h).trans (tsupport_mul_subset_left.trans hχt)
  obtain ⟨he,φ,F,R,hR,hφ,hF,hFS,hFd,hFh,hFg,hφt,hdec⟩ :=
    compact_projection_sobolev hA hA0 hhe hhc
  let p := compactJumpField (he.toLp e)
  let G := fun x => v.grad x - p x
  let f₀ := fun x => (1-χ x)*v.u x + φ x
  have hpe : p =ᵐ[volume] fun x => e x - compactGradientProjection (he.toLp e) x := by
    filter_upwards [Lp.coeFn_sub (he.toLp e) (compactGradientProjection (he.toLp e)),
      he.coeFn_toLp] with x hx hy
    change (he.toLp e) x = e x at hy
    simpa only [p,compactJumpField, Pi.sub_apply,hy] using hx
  have hfS : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → SobolevOn f₀ G (S \ B) := by
    intro S hS hb
    have hs := (hk S hS hb).add ((hφ S hS hb).mono sdiff_subset)
    apply hs.congr_gradient
    apply ae_restrict_of_ae
    filter_upwards [hpe] with x hx
    dsimp [G]
    rw [hx]
    dsimp [e]
    simp only [Complex.ofReal_sub, Complex.ofReal_one]
    ring
  have hGL : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → MemLp G 2 (volume.restrict S) := by
    intro S hS hb
    have hm := (hv.1.2.2.2 S hS hb).2.1
    rw [restrict_diff_null_set hH0] at hm
    exact hm.sub ((Lp.memLp p).restrict S)
  have hfL : LocallyIntegrable f₀ volume := by
    intro x
    refine ⟨ball x 1, ball_mem_nhds x zero_lt_one, ?_⟩
    have hf := (hfS (ball x 1) isOpen_ball isBounded_ball).1
    rw [restrict_diff_null_set hB0] at hf
    have : IsFiniteMeasure (volume.restrict (ball x 1)) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    exact hf.integrable (by norm_num)
  have hdiv (ψ : ℂ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
      (∫ x : ℂ, inner ℝ (G x) (gradient ψ x)) = 0 := by
    have hm := global_minimizer_divergence_free hv hψ hc
    have hp := compactJumpField_divergence_free (he.toLp e) hψ hc
    change (∫ x : ℂ, inner ℝ (v.grad x - p x) (gradient ψ x)) = 0
    simp_rw [inner_sub_left]
    rw [integral_sub hm.1
      (integrable_inner_memLp_measure (Lp.memLp p) (memLp_gradient_of_test hψ hc)), hm.2, hp]
    simp
  obtain ⟨f,hfe,hfs,hfh,hfS',hfg⟩ := local_sobolev_divergence_free_regular hB.isOpen_compl
    (by simpa only [sdiff_eq] using hfS) hGL hfL (fun ψ hψ hc _ => hdiv ψ hψ hc)
  refine ⟨h,e,he,φ,F,f,R,hhe,hhc,hht,hR,hφ,hF,hFS,hFd,hFh,hFg,hφt,hdec,
    hfs,hfh,?_,hfg,?_,hdiv⟩
  · simpa only [sdiff_eq] using hfS'
  · filter_upwards [hfe,hF] with x hx hy
    dsimp only [Pi.add_apply,Pi.sub_apply] at *
    rw [hx,hy]
    dsimp [f₀,h]
    ring

theorem testable_compact_projection_sobolev {A : Set ℂ} {h : ℂ → ℝ} {e : ℂ → ℂ}
    (hA : IsCompact A) (hA0 : volume A = 0) (hh : SobolevOn h e Aᶜ)
    (hc : IsCompact (essentialSupport h)) :
    ∃ he : MemLp e 2 volume, ∃ φ F : ℂ → ℝ, ∃ R : ℝ,
      0 < R ∧
      (∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S →
        SobolevOn φ (compactGradientProjection (he.toLp e)) S) ∧
      F =ᵐ[volume] h - φ ∧
      (∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S →
        SobolevOn F (compactJumpField (he.toLp e)) (S \ A)) ∧
      ContDiffOn ℝ ∞ F {z | R < ‖z‖} ∧ HarmonicOnNhd F {z | R < ‖z‖} ∧
      (∀ᵐ x ∂volume, R < ‖x‖ → gradient F x = compactJumpField (he.toLp e) x) ∧
      Tendsto φ (cocompact ℂ) (𝓝 0) ∧
      (∀ k : ℕ, ∃ C : ℝ, ∀ᶠ z in cocompact ℂ,
        ‖iteratedFDeriv ℝ k F z‖ ≤ C * ‖z‖⁻¹ ^ (k+1)) ∧
      CompactDivergenceTestable φ (compactGradientProjection (he.toLp e)) ∧
      (∀ᵐ x ∂volume, R < ‖x‖ → gradient φ x = compactGradientProjection (he.toLp e) x) ∧
      (∀ k : ℕ, ∃ C : ℝ, ∀ᶠ z in cocompact ℂ,
        ‖iteratedFDeriv ℝ k φ z‖ ≤ C * ‖z‖⁻¹ ^ (k+1)) := by
  classical
  have hmu : volume.restrict Aᶜ = volume :=
    Measure.restrict_eq_self_of_ae_mem (compl_mem_ae_iff.mpr hA0)
  have he : MemLp e 2 volume := by simpa [hmu] using hh.2.1
  obtain ⟨R0,hR0,he0⟩ := compact_support_weak_gradient hA hh hc
  have heL : ∀ᵐ x ∂volume, R0 < ‖x‖ → (he.toLp e) x = 0 := by
    filter_upwards [he.coeFn_toLp, he0] with x hx hz
    simpa [hx] using hz
  obtain ⟨φ,hφ,hφT,hφs,hφh,hφg,hφt,hφd⟩ := projection_has_testable_normalized_exterior_potential (he.toLp e) heL
  obtain ⟨R1,hR1,hb⟩ := hc.isBounded.exists_pos_norm_lt
  let R := max R0 R1
  let h0 := (essentialSupport h).indicator h
  let F := fun x => h0 x - φ x
  have hh0 : h0 =ᵐ[volume] h := by
    exact indicator_ae_eq_of_restrict_compl_ae_eq_zero
      (isClosed_essentialSupport h).measurableSet (ae_zero_compl_essentialSupport h)
  have hFeq : F =ᵐ[volume] h - φ := by
    filter_upwards [hh0] with x hx
    exact congrArg (fun t => t - φ x) hx
  have hFeq' : EqOn F (-φ) {z : ℂ | R < ‖z‖} := by
    intro z hz
    have hznot : z ∉ essentialSupport h := by
      intro hzs
      have := hb z hzs
      have : R1 < ‖z‖ := lt_of_le_of_lt (le_max_right _ _) hz
      linarith [hb z hzs]
    simp [F, h0, Set.indicator_of_notMem hznot]
  have hRsub : {z : ℂ | R < ‖z‖} ⊆ {z | R0 < ‖z‖} := by
    intro z hz
    exact lt_of_le_of_lt (le_max_left R0 R1) (show max R0 R1 < ‖z‖ from hz)
  refine ⟨he, φ, F, R, lt_of_lt_of_le hR0 (le_max_left _ _), hφ, hFeq, ?_, ?_, ?_, ?_,hφt,?_,hφT,?_,hφd⟩
  · intro S hS hbS
    have hhs := hh.mono (show S \ A ⊆ Aᶜ from fun _ hx => hx.2)
    have hfs := (hφ S hS hbS).mono (show S \ A ⊆ S from sdiff_subset)
    have hgrad : (e - compactGradientProjection (he.toLp e) : ℂ → ℂ) =ᵐ[volume]
        compactJumpField (he.toLp e) := by
      filter_upwards [he.coeFn_toLp, Lp.coeFn_sub (he.toLp e) (compactGradientProjection (he.toLp e))]
        with x hx hy
      simpa only [compactJumpField, Pi.sub_apply, hx] using hy.symm
    exact ((hhs.sub hfs).congr_ae hFeq).congr_gradient (ae_restrict_of_ae hgrad)
  · apply (hφs.mono hRsub).neg.congr
    exact hFeq'
  · intro z hz
    have hn : F =ᶠ[𝓝 z] -φ := hFeq'.eventuallyEq_of_mem
      ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)
    exact (harmonicAt_congr_nhds hn).mpr ((hφh z (hRsub hz)).neg)
  · filter_upwards [heL,hφg,Lp.coeFn_sub (he.toLp e) (compactGradientProjection (he.toLp e))]
      with z hez hg hp hz
    have hz0 : R0 < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hz
    have hn : F =ᶠ[𝓝 z] -φ := hFeq'.eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)
    rw [show gradient F z = -gradient φ z by
      simp only [gradient, hn.fderiv_eq, fderiv_neg, map_neg]]
    simp only [compactJumpField, hp, Pi.sub_apply, hez hz0, zero_sub, hg hz0]
  · intro k
    obtain ⟨C,hC⟩ := hφd k
    refine ⟨C,?_⟩
    have hext : ∀ᶠ z : ℂ in cocompact ℂ, R < ‖z‖ := by
      have hh := (isCompact_closedBall (0 : ℂ) R).compl_mem_cocompact
      filter_upwards [hh] with z hz
      simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using hz
    filter_upwards [hC,hext] with z hz hcZ
    have hn : F =ᶠ[𝓝 z] -φ := hFeq'.eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hcZ)
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hn k).eq_of_nhds]
    simpa only [iteratedFDeriv_neg, Pi.neg_apply, norm_neg] using hz
  · filter_upwards [hφg] with x hx hz
    exact hx (hRsub hz)

theorem minimizer_testable_harmonic_decomposition {v : Pair} (hv : GlobalAbsoluteMinimizer v)
    {A B : Set ℂ} (hA : IsCompact A) (hB : IsClosed B)
    (hAB : Disjoint A B) (hH : v.K = A ∪ B) :
    ∃ h : ℂ → ℝ, ∃ e : ℂ → ℂ, ∃ he : MemLp e 2 volume,
      ∃ φ F f : ℂ → ℝ, ∃ R : ℝ,
      SobolevOn h e Aᶜ ∧ IsCompact (essentialSupport h) ∧ essentialSupport h ⊆ Bᶜ ∧
      0 < R ∧
      (∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S →
        SobolevOn φ (compactGradientProjection (he.toLp e)) S) ∧
      F =ᵐ[volume] h - φ ∧
      (∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S →
        SobolevOn F (compactJumpField (he.toLp e)) (S \ A)) ∧
      ContDiffOn ℝ ∞ F {z | R < ‖z‖} ∧ HarmonicOnNhd F {z | R < ‖z‖} ∧
      (∀ᵐ x ∂volume, R < ‖x‖ → gradient F x = compactJumpField (he.toLp e) x) ∧
      Tendsto φ (cocompact ℂ) (𝓝 0) ∧
      (∀ k : ℕ, ∃ C : ℝ, ∀ᶠ z in cocompact ℂ,
        ‖iteratedFDeriv ℝ k F z‖ ≤ C * ‖z‖⁻¹ ^ (k+1)) ∧
      ContDiffOn ℝ ∞ f Bᶜ ∧ HarmonicOnNhd f Bᶜ ∧
      (∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S →
        SobolevOn f (fun x => v.grad x - compactJumpField (he.toLp e) x) (S \ B)) ∧
      (∀ᵐ x ∂volume, x ∉ B → gradient f x = v.grad x - compactJumpField (he.toLp e) x) ∧
      v.u =ᵐ[volume] f + F ∧
      (∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        (∫ x : ℂ, inner ℝ (v.grad x - compactJumpField (he.toLp e) x) (gradient ψ x)) = 0) ∧
      CompactDivergenceTestable φ (compactGradientProjection (he.toLp e)) ∧
      (∀ᵐ x ∂volume, R < ‖x‖ → gradient φ x = compactGradientProjection (he.toLp e) x) ∧
      (∀ k : ℕ, ∃ C : ℝ, ∀ᶠ z in cocompact ℂ,
        ‖iteratedFDeriv ℝ k φ z‖ ≤ C * ‖z‖⁻¹ ^ (k+1)) := by
  have hH0 : volume v.K = 0 := volume_eq_zero_of_locally_finite_length hv.1.2.2.1
  have hA0 : volume A = 0 := measure_mono_null (by rw [hH]; exact subset_union_left) hH0
  have hB0 : volume B = 0 := measure_mono_null (by rw [hH]; exact subset_union_right) hH0
  obtain ⟨χ,hχ,hχc,hχt,hχ1,hχr⟩ := compact_smooth_cutoff hA hB.isOpen_compl
    (Set.disjoint_left.mp hAB)
  let h := fun x => χ x * v.u x
  let e := fun x => χ x • v.grad x + v.u x • gradient χ x
  obtain ⟨hhe,hhc,hk⟩ := cutoff_sobolev_decomposition hv.1 hA hB hH hχ hχc hχt hχ1
  have hht : essentialSupport h ⊆ Bᶜ :=
    (essentialSupport_subset_tsupport h).trans (tsupport_mul_subset_left.trans hχt)
  obtain ⟨he,φ,F,R,hR,hφ,hF,hFS,hFd,hFh,hFg,hφt,hdec,hφT,hφg,hφdec⟩ :=
    testable_compact_projection_sobolev hA hA0 hhe hhc
  let p := compactJumpField (he.toLp e)
  let G := fun x => v.grad x - p x
  let f₀ := fun x => (1-χ x)*v.u x + φ x
  have hpe : p =ᵐ[volume] fun x => e x - compactGradientProjection (he.toLp e) x := by
    filter_upwards [Lp.coeFn_sub (he.toLp e) (compactGradientProjection (he.toLp e)),
      he.coeFn_toLp] with x hx hy
    change (he.toLp e) x = e x at hy
    simpa only [p,compactJumpField, Pi.sub_apply,hy] using hx
  have hfS : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → SobolevOn f₀ G (S \ B) := by
    intro S hS hb
    have hs := (hk S hS hb).add ((hφ S hS hb).mono sdiff_subset)
    apply hs.congr_gradient
    apply ae_restrict_of_ae
    filter_upwards [hpe] with x hx
    dsimp [G]
    rw [hx]
    dsimp [e]
    simp only [Complex.ofReal_sub, Complex.ofReal_one]
    ring
  have hGL : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → MemLp G 2 (volume.restrict S) := by
    intro S hS hb
    have hm := (hv.1.2.2.2 S hS hb).2.1
    rw [restrict_diff_null_set hH0] at hm
    exact hm.sub ((Lp.memLp p).restrict S)
  have hfL : LocallyIntegrable f₀ volume := by
    intro x
    refine ⟨ball x 1, ball_mem_nhds x zero_lt_one, ?_⟩
    have hf := (hfS (ball x 1) isOpen_ball isBounded_ball).1
    rw [restrict_diff_null_set hB0] at hf
    have : IsFiniteMeasure (volume.restrict (ball x 1)) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    exact hf.integrable (by norm_num)
  have hdiv (ψ : ℂ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
      (∫ x : ℂ, inner ℝ (G x) (gradient ψ x)) = 0 := by
    have hm := global_minimizer_divergence_free hv hψ hc
    have hp := compactJumpField_divergence_free (he.toLp e) hψ hc
    change (∫ x : ℂ, inner ℝ (v.grad x - p x) (gradient ψ x)) = 0
    simp_rw [inner_sub_left]
    rw [integral_sub hm.1
      (integrable_inner_memLp_measure (Lp.memLp p) (memLp_gradient_of_test hψ hc)), hm.2, hp]
    simp
  obtain ⟨f,hfe,hfs,hfh,hfS',hfg⟩ := local_sobolev_divergence_free_regular hB.isOpen_compl
    (by simpa only [sdiff_eq] using hfS) hGL hfL (fun ψ hψ hc _ => hdiv ψ hψ hc)
  refine ⟨h,e,he,φ,F,f,R,hhe,hhc,hht,hR,hφ,hF,hFS,hFd,hFh,hFg,hφt,hdec,
    hfs,hfh,?_,hfg,?_,hdiv,hφT,hφg,hφdec⟩
  · simpa only [sdiff_eq] using hfS'
  · filter_upwards [hfe,hF] with x hx hy
    dsimp only [Pi.add_apply,Pi.sub_apply] at *
    rw [hx,hy]
    dsimp [f₀,h]
    ring

end MumfordShah
end

end OAI
