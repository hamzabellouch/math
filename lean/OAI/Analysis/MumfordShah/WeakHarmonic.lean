import Mathlib
import OAI.Analysis.MumfordShah.GradientProjection

namespace OAI

/-! MumfordShah weak harmonic. -/

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

instance : CompleteSpace compactGradientClosure := by
  unfold compactGradientClosure
  infer_instance

instance : CompleteSpace compactGradientClosure := by
  unfold compactGradientClosure
  infer_instance

def WeakHarmonicOn (u : ℂ → ℝ) (O : Set ℂ) : Prop :=
  ∀ ζ : ℂ → ℝ, ContDiff ℝ ∞ ζ → HasCompactSupport ζ → tsupport ζ ⊆ O →
    ∫ x, u x * (Δ ζ) x = 0

lemma harmonic_angle_integral {f : ℂ → ℝ} {c : ℂ} {r : ℝ}
    (hf : HarmonicOnNhd f (closedBall c |r|)) :
    (∫ θ in (-Real.pi)..Real.pi, f (circleMap c r θ)) = 2 * Real.pi * f c := by
  have hm := hf.circleAverage_eq
  rw [Real.circleAverage_eq_integral_add (-Real.pi),
    intervalIntegral.integral_comp_add_right (fun θ => f (circleMap c r θ))] at hm
  simp only [zero_add, show 2 * Real.pi + -Real.pi = Real.pi by ring,
    smul_eq_mul] at hm
  have hp : 2 * Real.pi ≠ 0 := by positivity
  exact (inv_mul_eq_iff_eq_mul₀ hp).mp hm

lemma polar_weight_integrable {k f : ℂ → ℝ} {R : ℝ} (hk : Continuous k)
    (hf : Continuous f) (hks : Function.support k ⊆ closedBall 0 R) (c : ℂ) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * k (Complex.polarCoord.symm p) *
      f (c + Complex.polarCoord.symm p)) polarCoord.target := by
  let g : ℝ × ℝ → ℝ := fun p => p.1 * k (Complex.polarCoord.symm p) *
    f (c + Complex.polarCoord.symm p)
  have hc : Continuous g := by
    simp only [g, Complex.polarCoord_symm_apply]
    fun_prop
  apply IntegrableOn.of_inter_support polarCoord.open_target.measurableSet
  apply (hc.continuousOn.integrableOn_compact ((isCompact_Icc : IsCompact (Icc (0 : ℝ) R)).prod
    (isCompact_Icc : IsCompact (Icc (-Real.pi) Real.pi)))).mono_set
  intro p hp
  have hpt : 0 < p.1 ∧ p.2 ∈ Ioo (-Real.pi) Real.pi := hp.1
  have hkn : k (Complex.polarCoord.symm p) ≠ 0 := by
    intro hz
    apply hp.2
    change p.1 * k (Complex.polarCoord.symm p) * f (c + Complex.polarCoord.symm p) = 0
    rw [hz, mul_zero, zero_mul]
  have hrs := hks hkn
  simp only [mem_closedBall, dist_zero_right, Complex.norm_polarCoord_symm,
    abs_of_pos hpt.1] at hrs
  exact ⟨⟨hpt.1.le, hrs⟩, ⟨hpt.2.1.le, hpt.2.2.le⟩⟩

lemma radial_weighted_harmonic_mean {k f : ℂ → ℝ} {R : ℝ} {c : ℂ}
    (hk : Continuous k) (hf : Continuous f)
    (hks : Function.support k ⊆ closedBall 0 R)
    (hrad : ∀ z w : ℂ, ‖z‖ = ‖w‖ → k z = k w)
    (harm : HarmonicOnNhd f (closedBall c R)) :
    (∫ z, k z * f (c + z)) = (∫ z, k z) * f c := by
  rw [← integral_mul_const]
  rw [← Complex.integral_comp_polarCoord_symm (fun z => k z * f (c + z)),
    ← Complex.integral_comp_polarCoord_symm (fun z => k z * f c)]
  simp only [polarCoord_target, smul_eq_mul, ← mul_assoc]
  have hi := polar_weight_integrable hk hf hks c
  have hj := polar_weight_integrable hk (continuous_const (y := f c)) hks c
  simp only [polarCoord_target] at hi hj
  simp only [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hi hj ⊢
  rw [integral_prod _ hi, integral_prod _ hj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hrp : 0 < r := hr
  have hnorm : ∀ θ : ℝ, ‖Complex.polarCoord.symm (r, θ)‖ = ‖(r : ℂ)‖ := by
    intro θ
    simp
  have hkr : ∀ θ : ℝ, k (Complex.polarCoord.symm (r, θ)) = k (r : ℂ) :=
    fun θ => hrad _ _ (hnorm θ)
  simp only [hkr]
  by_cases hrR : r ≤ R
  · have hh : HarmonicOnNhd f (closedBall c |r|) :=
      harm.mono (closedBall_subset_closedBall (by simpa [abs_of_pos hrp] using hrR))
    have hp : ∀ θ : ℝ, c + Complex.polarCoord.symm (r, θ) = circleMap c r θ := by
      intro θ
      simp [circleMap, Complex.polarCoord_symm_apply, Complex.exp_mul_I]
    simp_rw [hp]
    rw [integral_const_mul, integral_const_mul]
    congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      harmonic_angle_integral hh]
    simp [Measure.real, Real.pi_pos.le]
    ring_nf
    simp
  · have hz : k (r : ℂ) = 0 := by
      by_contra hn
      have := hks hn
      simp only [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hrp] at this
      exact hrR this
    simp [hz]

def radialBump (r : ℝ) (z : ℂ) : ℝ :=
  (ContDiffBumpBase.ofInnerProductSpace ℂ).toFun 2 (r⁻¹ • z)

lemma radialBump_contDiff (r : ℝ) : ContDiff ℝ ∞ (radialBump r) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  have h := (ContDiffBumpBase.ofInnerProductSpace ℂ).smooth.contDiffAt
    ((isOpen_Ioi.prod isOpen_univ).mem_nhds (show (2, r⁻¹ • z) ∈
      Ioi (1 : ℝ) ×ˢ (univ : Set ℂ) by norm_num))
  have hh : ContDiffAt ℝ ∞ (fun w : ℂ => ((2 : ℝ), r⁻¹ • w)) z := by fun_prop
  have hh2 := h.comp z hh
  exact hh2

lemma radialBump_radial (r : ℝ) (z w : ℂ) (h : ‖z‖ = ‖w‖) :
    radialBump r z = radialBump r w := by
  simp only [radialBump, ContDiffBumpBase.ofInnerProductSpace, norm_smul, h]

lemma radialBump_nonneg (r : ℝ) (z : ℂ) : 0 ≤ radialBump r z :=
  ((ContDiffBumpBase.ofInnerProductSpace ℂ).mem_Icc 2 (r⁻¹ • z)).1

lemma radialBump_support {r : ℝ} (hr : 0 < r) :
    Function.support (radialBump r) = ball 0 (2 * r) := by
  ext z
  change (r⁻¹ • z) ∈ Function.support ((ContDiffBumpBase.ofInnerProductSpace ℂ).toFun 2) ↔ _
  rw [(ContDiffBumpBase.ofInnerProductSpace ℂ).support 2 (by norm_num)]
  simp only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  rw [← div_eq_inv_mul, div_lt_iff₀ hr]

lemma radialBump_compact {r : ℝ} (hr : 0 < r) : HasCompactSupport (radialBump r) := by
  unfold HasCompactSupport tsupport
  rw [radialBump_support hr, closure_ball _ (by positivity : 2 * r ≠ 0)]
  exact isCompact_closedBall _ _

lemma radialBump_integral_pos {r : ℝ} (hr : 0 < r) :
    0 < ∫ z, radialBump r z := by
  have hi : Integrable (radialBump r) volume :=
    (radialBump_contDiff r).continuous.integrable_of_hasCompactSupport (radialBump_compact hr)
  rw [integral_pos_iff_support_of_nonneg (radialBump_nonneg r) hi, radialBump_support hr]
  exact measure_ball_pos volume 0 (by positivity)

def radialMollifier (r : ℝ) (z : ℂ) : ℝ :=
  radialBump r z / ∫ w, radialBump r w

lemma radialMollifier_contDiff (r : ℝ) : ContDiff ℝ ∞ (radialMollifier r) :=
  (radialBump_contDiff r).div_const _

lemma radialMollifier_radial (r : ℝ) (z w : ℂ) (h : ‖z‖ = ‖w‖) :
    radialMollifier r z = radialMollifier r w := by
  simp only [radialMollifier, radialBump_radial r z w h]

lemma radialMollifier_compact {r : ℝ} (hr : 0 < r) : HasCompactSupport (radialMollifier r) :=
by
  change HasCompactSupport (fun z => radialBump r z * (∫ w, radialBump r w)⁻¹)
  exact (radialBump_compact hr).mul_right

lemma radialMollifier_integral {r : ℝ} (hr : 0 < r) : ∫ z, radialMollifier r z = 1 := by
  simp only [radialMollifier, integral_div]
  exact div_self (radialBump_integral_pos hr).ne'

lemma convolution_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {u : ℂ → ℝ} {k : ℂ → E}
    (hu : LocallyIntegrable u volume) (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k) :
    fderiv ℝ (u ⋆[lsmul ℝ ℝ, volume] k) =
      u ⋆[(lsmul ℝ ℝ).precompR ℂ, volume] (fderiv ℝ k) := by
  funext x
  exact (hc.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hu (hk.of_le (by norm_num)) x).fderiv

lemma convolution_fderiv_apply {u k : ℂ → ℝ}
    (hu : LocallyIntegrable u volume) (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k)
    (x v : ℂ) :
    fderiv ℝ (u ⋆[lsmul ℝ ℝ, volume] k) x v =
      (u ⋆[lsmul ℝ ℝ, volume] (fun y => fderiv ℝ k y v)) x := by
  rw [convolution_fderiv hu hk hc]
  exact convolution_precompR_apply _ hu (hc.fderiv ℝ)
    (hk.fderiv_right (by simp) : ContDiff ℝ ∞ (fderiv ℝ k)).continuous x v

lemma smooth_directional {k : ℂ → ℝ} (hk : ContDiff ℝ ∞ k) (v : ℂ) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ k y v) := by
  exact (hk.fderiv_right (by simp)).clm_apply contDiff_const

lemma compact_directional {k : ℂ → ℝ} (hc : HasCompactSupport k) (v : ℂ) :
    HasCompactSupport (fun y => fderiv ℝ k y v) :=
  (hc.fderiv ℝ).comp_left (g := fun l : ℂ →L[ℝ] ℝ => l v) (show (fun l : ℂ →L[ℝ] ℝ => l v) 0 = 0 from rfl)

lemma fderiv_directional {k : ℂ → ℝ} (hk : ContDiff ℝ ∞ k) (x v w : ℂ) :
    fderiv ℝ (fun y => fderiv ℝ k y v) x w = fderiv ℝ (fderiv ℝ k) x w v := by
  have hd : Differentiable ℝ (fderiv ℝ k) :=
    (hk.fderiv_right (by simp) : ContDiff ℝ ∞ (fderiv ℝ k)).differentiable (by simp)
  have h := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp x (hd x).hasFDerivAt
  exact congrArg (fun l : ℂ →L[ℝ] ℝ => l w) h.fderiv

lemma convolution_second_directional {u k : ℂ → ℝ}
    (hu : LocallyIntegrable u volume) (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k)
    (x v : ℂ) :
    fderiv ℝ (fun y => fderiv ℝ (u ⋆[lsmul ℝ ℝ, volume] k) y v) x v =
      (u ⋆[lsmul ℝ ℝ, volume] (fun y => fderiv ℝ (fderiv ℝ k) y v v)) x := by
  have he : (fun y => fderiv ℝ (u ⋆[lsmul ℝ ℝ, volume] k) y v) =
      u ⋆[lsmul ℝ ℝ, volume] (fun y => fderiv ℝ k y v) :=
    funext fun y => convolution_fderiv_apply hu hk hc y v
  rw [he, convolution_fderiv_apply hu (smooth_directional hk v) (compact_directional hc v)]
  simp only [fderiv_directional hk]

lemma integrable_second_component {u k : ℂ → ℝ}
    (hu : LocallyIntegrable u volume) (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k)
    (x v : ℂ) :
    Integrable (fun y => u y * fderiv ℝ (fderiv ℝ k) (x - y) v v) volume := by
  have h := (compact_directional (compact_directional hc v) v).convolutionExists_right
    (lsmul ℝ ℝ) hu (smooth_directional (smooth_directional hk v) v).continuous x
  simpa only [ConvolutionExistsAt, fderiv_directional hk, lsmul_apply, smul_eq_mul] using h

lemma laplacian_convolution {u k : ℂ → ℝ}
    (hu : LocallyIntegrable u volume) (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k) :
    Δ (u ⋆[lsmul ℝ ℝ, volume] k) = u ⋆[lsmul ℝ ℝ, volume] (Δ k) := by
  have hs : ContDiff ℝ ∞ (u ⋆[lsmul ℝ ℝ, volume] k) :=
    hc.contDiff_convolution_right (lsmul ℝ ℝ) hu hk
  funext x
  simp only [laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [← fderiv_directional hs x 1 1, ← fderiv_directional hs x Complex.I Complex.I,
    convolution_second_directional hu hk hc, convolution_second_directional hu hk hc]
  simp only [convolution_def, lsmul_apply, smul_eq_mul]
  rw [← integral_add (integrable_second_component hu hk hc x 1)
    (integrable_second_component hu hk hc x Complex.I)]
  simp only [mul_add]

lemma iteratedFDeriv_two_comp_neg {k : ℂ → ℝ} (hk : ContDiff ℝ ∞ k) (y v : ℂ) :
    iteratedFDeriv ℝ 2 (fun z => k (-z)) y ![v,v] =
      iteratedFDeriv ℝ 2 k (-y) ![v,v] := by
  have h := (-ContinuousLinearMap.id ℝ ℂ).iteratedFDeriv_comp_right (n := ∞) hk y
    (i := 2) (by exact WithTop.coe_le_coe.mpr le_top)
  have he := congrArg (fun d : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ℂ) ℝ => d ![v,v]) h
  simp only [neg_apply, id_apply, Function.comp_def,
    ContinuousMultilinearMap.compContinuousLinearMap_apply] at he
  rw [he]
  have hv : (fun x : Fin 2 => - (![v,v] x)) = fun x => (-1 : ℝ) • (![v,v] x) := by
    ext x
    simp
  rw [hv, ContinuousMultilinearMap.map_smul_univ]
  simp

lemma laplacian_comp_sub_left {k : ℂ → ℝ} (hk : ContDiff ℝ ∞ k) (x y : ℂ) :
    Δ (fun z => k (x - z)) y = Δ k (x - y) := by
  have ha : ContDiff ℝ ∞ (fun z => k (x + z)) := hk.comp (by fun_prop)
  simp only [laplacian_eq_iteratedFDeriv_complexPlane]
  change iteratedFDeriv ℝ 2 (fun z => (fun a => k (x + a)) (-z)) y ![1,1] +
    iteratedFDeriv ℝ 2 (fun z => (fun a => k (x + a)) (-z)) y ![Complex.I, Complex.I] = _
  rw [iteratedFDeriv_two_comp_neg ha, iteratedFDeriv_two_comp_neg ha,
    iteratedFDeriv_comp_add_left]
  rfl

lemma convolution_assoc_compact {u k l : ℂ → ℝ}
    (hu : LocallyIntegrable u volume) (hk : Continuous k) (hl : Continuous l)
    (hck : HasCompactSupport k) (hcl : HasCompactSupport l) :
    (u ⋆[lsmul ℝ ℝ, volume] k) ⋆[lsmul ℝ ℝ, volume] l =
      u ⋆[lsmul ℝ ℝ, volume] (k ⋆[lsmul ℝ ℝ, volume] l) := by
  have hun : LocallyIntegrable (fun x => ‖u x‖) volume :=
    locallyIntegrableOn_univ.mp (hu.locallyIntegrableOn univ).norm
  funext x
  apply convolution_assoc (lsmul ℝ ℝ) (lsmul ℝ ℝ) (lsmul ℝ ℝ) (lsmul ℝ ℝ)
      (fun a b c => by simp only [lsmul_apply, smul_eq_mul]; ring)
      hu.aestronglyMeasurable hk.aestronglyMeasurable hl.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (hck.convolutionExists_right _ hu hk)
  · exact Filter.Eventually.of_forall ((hcl.norm).convolutionExists_right _
      hk.norm.locallyIntegrable hl.norm)
  · exact ((hck.norm).convolution (ContinuousLinearMap.mul ℝ ℝ) (hcl.norm)).convolutionExists_right
      (ContinuousLinearMap.mul ℝ ℝ) hun
      ((hcl.norm).continuous_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
        hk.norm.locallyIntegrable hl.norm) x

lemma scalar_convolution_comm (u k : ℂ → ℝ) :
    u ⋆[lsmul ℝ ℝ, volume] k = k ⋆[lsmul ℝ ℝ, volume] u := by
  have h : (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip = lsmul ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro a
    apply ContinuousLinearMap.ext
    intro b
    exact mul_comm b a
  rw [← convolution_flip, h]

lemma convolution_exchange_compact {u k l : ℂ → ℝ}
    (hu : LocallyIntegrable u volume) (hk : Continuous k) (hl : Continuous l)
    (hck : HasCompactSupport k) (hcl : HasCompactSupport l) :
    (u ⋆[lsmul ℝ ℝ, volume] k) ⋆[lsmul ℝ ℝ, volume] l =
      (u ⋆[lsmul ℝ ℝ, volume] l) ⋆[lsmul ℝ ℝ, volume] k := by
  rw [convolution_assoc_compact hu hk hl hck hcl,
    scalar_convolution_comm k l, ← convolution_assoc_compact hu hl hk hcl hck]

lemma tsupport_sub_left {k : ℂ → ℝ} {S : ℝ}
    (hk : tsupport k ⊆ closedBall 0 S) (x : ℂ) :
    tsupport (fun y => k (x - y)) ⊆ closedBall x S := by
  apply closure_minimal _ isClosed_closedBall
  intro y hy
  have hm := hk (subset_tsupport k hy)
  simpa only [mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero, norm_sub_rev] using hm

lemma closedBall_subset_inner_ball {c x : ℂ} {R S : ℝ}
    (hx : x ∈ ball c (R - S)) : closedBall x S ⊆ ball c R := by
  intro y hy
  have htri := dist_triangle y x c
  simp only [mem_ball, mem_closedBall] at *
  linarith

lemma weak_harmonic_convolution_laplacian {u k : ℂ → ℝ} {c x : ℂ} {R S : ℝ}
    (hu : LocallyIntegrable u volume) (hw : WeakHarmonicOn u (ball c R))
    (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k)
    (hks : tsupport k ⊆ closedBall 0 S) (hx : x ∈ ball c (R-S)) :
    Δ (u ⋆[lsmul ℝ ℝ, volume] k) x = 0 := by
  rw [laplacian_convolution hu hk hc]
  have htest : ContDiff ℝ ∞ (fun y => k (x-y)) := hk.comp (by fun_prop)
  have htc : HasCompactSupport (fun y => k (x-y)) :=
    hc.comp_homeomorph (Homeomorph.subLeft x)
  have hts := (tsupport_sub_left hks x).trans (closedBall_subset_inner_ball hx)
  have h := hw _ htest htc hts
  simpa only [convolution_def, lsmul_apply, smul_eq_mul, laplacian_comp_sub_left hk] using h

lemma weak_harmonic_convolution {u k : ℂ → ℝ} {c : ℂ} {R S : ℝ}
    (hu : LocallyIntegrable u volume) (hw : WeakHarmonicOn u (ball c R))
    (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k)
    (hks : tsupport k ⊆ closedBall 0 S) :
    HarmonicOnNhd (u ⋆[lsmul ℝ ℝ, volume] k) (ball c (R-S)) := by
  intro x hx
  have hs := hc.contDiff_convolution_right (lsmul ℝ ℝ) hu hk
  refine ⟨hs.contDiffAt.of_le (by exact WithTop.coe_le_coe.mpr le_top), ?_⟩
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  exact weak_harmonic_convolution_laplacian hu hw hk hc hks hy

lemma radialMollifier_support {r : ℝ} (hr : 0 < r) :
    Function.support (radialMollifier r) = ball 0 (2*r) := by
  rw [← radialBump_support hr]
  ext z
  simp [Function.mem_support, radialMollifier, (radialBump_integral_pos hr).ne']

lemma radialMollifier_reproduces {f : ℂ → ℝ} {r : ℝ} {c : ℂ}
    (hr : 0 < r) (hf : Continuous f)
    (hh : HarmonicOnNhd f (closedBall c (2*r))) :
    (f ⋆[lsmul ℝ ℝ, volume] radialMollifier r) c = f c := by
  rw [scalar_convolution_comm]
  simp only [convolution_def, lsmul_apply, smul_eq_mul]
  rw [← integral_neg_eq_self]
  have he : (fun z : ℂ => radialMollifier r (-z) * f (c - -z)) =
      fun z => radialMollifier r z * f (c+z) := by
    funext z
    rw [radialMollifier_radial r (-z) z (norm_neg z), sub_neg_eq_add]
  rw [he]
  rw [radial_weighted_harmonic_mean (radialMollifier_contDiff r).continuous hf
    (by rw [radialMollifier_support hr]; exact ball_subset_closedBall)
    (radialMollifier_radial r) hh, radialMollifier_integral hr, one_mul]

def approxBump (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := 1 / (n+1)
  rOut := 2 / (n+1)
  rIn_pos := by positivity
  rIn_lt_rOut := by apply div_lt_div_of_pos_right (by norm_num); positivity

lemma approxBump_tendsto : Tendsto (fun n => (approxBump n).rOut) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => 2 / ((n:ℝ)+1)) atTop (𝓝 0)
  exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)

lemma ae_approxBump_convolution {u : ℂ → ℝ} (hu : LocallyIntegrable u volume) :
    ∀ᵐ x ∂volume, Tendsto (fun n => (u ⋆[lsmul ℝ ℝ, volume]
      (approxBump n).normed volume) x) atTop (𝓝 (u x)) := by
  simp_rw [scalar_convolution_comm u]
  apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable approxBump_tendsto
      (K := 2) _ hu
  exact Filter.Eventually.of_forall fun n => by simp only [approxBump]; ring_nf; rfl

lemma approxBump_convolution_continuous {u : ℂ → ℝ} (hu : Continuous u) (x : ℂ) :
    Tendsto (fun n => (u ⋆[lsmul ℝ ℝ, volume] (approxBump n).normed volume) x)
      atTop (𝓝 (u x)) := by
  simp_rw [scalar_convolution_comm u]
  exact ContDiffBump.convolution_tendsto_right_of_continuous approxBump_tendsto hu x

lemma radialMollifier_tsupport {r : ℝ} (hr : 0 < r) :
    tsupport (radialMollifier r) = closedBall 0 (2*r) := by
  rw [tsupport, radialMollifier_support hr, closure_ball _ (by positivity : 2*r ≠ 0)]

lemma weak_harmonic_ae_eq_radialConvolution {u : ℂ → ℝ} {c : ℂ} {R r : ℝ}
    (hr : 0 < r) (hu : LocallyIntegrable u volume)
    (hw : WeakHarmonicOn u (ball c R)) :
    u =ᵐ[volume.restrict (ball c (R-3*r))] u ⋆[lsmul ℝ ℝ, volume] radialMollifier r := by
  change ∀ᵐ x ∂volume.restrict (ball c (R-3*r)), u x =
    (u ⋆[lsmul ℝ ℝ, volume] radialMollifier r) x
  rw [ae_restrict_iff' measurableSet_ball]
  filter_upwards [ae_approxBump_convolution hu] with x hx
  intro hxc
  have hs := (radialMollifier_compact hr).contDiff_convolution_right (lsmul ℝ ℝ) hu
    (radialMollifier_contDiff r)
  have ht := approxBump_convolution_continuous hs.continuous x
  have he : ∀ᶠ n in atTop,
      ((u ⋆[lsmul ℝ ℝ, volume] radialMollifier r) ⋆[lsmul ℝ ℝ, volume]
        (approxBump n).normed volume) x =
      (u ⋆[lsmul ℝ ℝ, volume] (approxBump n).normed volume) x := by
    filter_upwards [approxBump_tendsto.eventually (gt_mem_nhds hr)] with n hn
    rw [convolution_exchange_compact hu (radialMollifier_contDiff r).continuous
      (approxBump n).continuous_normed (radialMollifier_compact hr)
      (approxBump n).hasCompactSupport_normed]
    apply radialMollifier_reproduces hr
      ((approxBump n).hasCompactSupport_normed.continuous_convolution_right _ hu
        (approxBump n).continuous_normed)
    apply (weak_harmonic_convolution hu hw (approxBump n).contDiff_normed
      (approxBump n).hasCompactSupport_normed
      (by rw [(approxBump n).tsupport_normed_eq])).mono
    apply closedBall_subset_inner_ball
    simp only [mem_ball] at hxc ⊢
    linarith
  exact tendsto_nhds_unique hx (ht.congr' he)

lemma convolution_local_congr {u v k : ℂ → ℝ} {c x : ℂ} {R S : ℝ}
    (he : u =ᵐ[volume.restrict (ball c R)] v)
    (hks : tsupport k ⊆ closedBall 0 S) (hx : x ∈ ball c (R-S)) :
    (u ⋆[lsmul ℝ ℝ, volume] k) x = (v ⋆[lsmul ℝ ℝ, volume] k) x := by
  have he' := (ae_restrict_iff' measurableSet_ball).mp he
  apply integral_congr_ae
  filter_upwards [he'] with y hy
  simp only [lsmul_apply, smul_eq_mul]
  by_cases hk : k (x-y) = 0
  · simp only [hk, mul_zero]
  · rw [hy ((closedBall_subset_inner_ball hx) ((tsupport_sub_left hks x)
      (subset_tsupport (fun z => k (x-z)) hk)))]

def harmonicRepresentative (u : ℂ → ℝ) (x : ℂ) : ℝ :=
  limUnder atTop (fun n => (u ⋆[lsmul ℝ ℝ, volume] (approxBump n).normed volume) x)

lemma harmonicRepresentative_ae {u : ℂ → ℝ} (hu : LocallyIntegrable u volume) :
    harmonicRepresentative u =ᵐ[volume] u := by
  filter_upwards [ae_approxBump_convolution hu] with x hx
  exact hx.limUnder_eq

lemma harmonicRepresentative_eq_local {u v : ℂ → ℝ} {c x : ℂ} {R : ℝ}
    (he : u =ᵐ[volume.restrict (ball c R)] v) (hv : Continuous v)
    (hx : x ∈ ball c R) : harmonicRepresentative u x = v x := by
  have ht := approxBump_convolution_continuous hv x
  have he' : ∀ᶠ n in atTop,
      (v ⋆[lsmul ℝ ℝ, volume] (approxBump n).normed volume) x =
      (u ⋆[lsmul ℝ ℝ, volume] (approxBump n).normed volume) x := by
    filter_upwards [approxBump_tendsto.eventually
      (gt_mem_nhds (sub_pos.mpr (show dist x c < R from hx)))] with n hn
    symm
    apply convolution_local_congr he (by rw [(approxBump n).tsupport_normed_eq])
    simp only [mem_ball]
    linarith
  exact (ht.congr' he').limUnder_eq

lemma WeakHarmonicOn.mono {u : ℂ → ℝ} {S O : Set ℂ}
    (hw : WeakHarmonicOn u O) (hSO : S ⊆ O) : WeakHarmonicOn u S := by
  intro ζ hζ hc hs
  exact hw ζ hζ hc (hs.trans hSO)

lemma harmonicRepresentative_regular {u : ℂ → ℝ} {O : Set ℂ}
    (hu : LocallyIntegrable u volume) (hO : IsOpen O) (hw : WeakHarmonicOn u O)
    {x : ℂ} (hx : x ∈ O) :
    ContDiffAt ℝ ∞ (harmonicRepresentative u) x ∧ HarmonicAt (harmonicRepresentative u) x := by
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hO x hx
  let r := R / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hwball := hw.mono hball
  have hs := (radialMollifier_compact hr).contDiff_convolution_right (lsmul ℝ ℝ) hu
    (radialMollifier_contDiff r)
  have hae := weak_harmonic_ae_eq_radialConvolution hr hu hwball
  have he : harmonicRepresentative u =ᶠ[𝓝 x] u ⋆[lsmul ℝ ℝ, volume] radialMollifier r := by
    have hxball : x ∈ ball x (R-3*r) := by
      apply mem_ball_self; dsimp [r]; linarith
    filter_upwards [isOpen_ball.mem_nhds hxball] with y hy
    exact harmonicRepresentative_eq_local hae hs.continuous hy
  refine ⟨hs.contDiffAt.congr_of_eventuallyEq he, (harmonicAt_congr_nhds he).mpr ?_⟩
  apply weak_harmonic_convolution hu hwball (radialMollifier_contDiff r)
    (radialMollifier_compact hr) (by rw [radialMollifier_tsupport hr])
  apply mem_ball_self
  dsimp [r]
  linarith

theorem weak_harmonic_regular {u : ℂ → ℝ} {O : Set ℂ}
    (hu : LocallyIntegrable u volume) (hO : IsOpen O) (hw : WeakHarmonicOn u O) :
    ∃ v : ℂ → ℝ, v =ᵐ[volume] u ∧ ContDiffOn ℝ ∞ v O ∧ HarmonicOnNhd v O := by
  refine ⟨harmonicRepresentative u, harmonicRepresentative_ae hu, ?_, ?_⟩
  · exact fun x hx => (harmonicRepresentative_regular hu hO hw hx).1.contDiffWithinAt
  · exact fun x hx => (harmonicRepresentative_regular hu hO hw hx).2

end MumfordShah
end

end OAI
