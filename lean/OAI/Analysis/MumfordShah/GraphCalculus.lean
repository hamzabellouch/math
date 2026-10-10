import Mathlib
import OAI.Analysis.MumfordShah.SobolevAlgebra

namespace OAI

/-! MumfordShah graph calculus. -/

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
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff

open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap

open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff

def graphChart (κ : ℝ → ℝ) (s r : ℝ) : ℂ := Complex.ofReal s + Complex.ofReal (κ s + r) * Complex.I

def graphSource (κ β η : ℝ → ℝ) (z : ℂ) : ℝ := β z.re * η (z.im-κ z.re)

def graphUpper (κ : ℝ → ℝ) : Set ℂ := {z | κ z.re < z.im}

def graphJump (κ β η : ℝ → ℝ) : ℂ → ℝ := (graphUpper κ).indicator (graphSource κ β η)

def graphJumpGradient (κ β η : ℝ → ℝ) : ℂ → ℂ :=
  (graphUpper κ).indicator (gradient (graphSource κ β η))

lemma graphSource_contDiff {κ β η : ℝ → ℝ}
    (hκ : ContDiff ℝ 1 κ) (hβ : ContDiff ℝ 1 β) (hη : ContDiff ℝ 1 η) :
    ContDiff ℝ 1 (graphSource κ β η) := by
  exact (hβ.comp Complex.reCLM.contDiff).mul
    (hη.comp (Complex.imCLM.contDiff.sub (hκ.comp Complex.reCLM.contDiff)))

lemma graphSource_compactSupport {κ β η : ℝ → ℝ} (hκ : Continuous κ)
    (hβ : HasCompactSupport β) (hη : HasCompactSupport η) :
    HasCompactSupport (graphSource κ β η) := by
  have hchart : Continuous (fun p : ℝ × ℝ => graphChart κ p.1 p.2) := by
    unfold graphChart
    fun_prop
  apply HasCompactSupport.of_support_subset_isCompact
    ((hβ.isCompact.prod hη.isCompact).image hchart)
  intro z hz
  have hb : β z.re ≠ 0 := left_ne_zero_of_mul (show graphSource κ β η z ≠ 0 from hz)
  have he : η (z.im-κ z.re) ≠ 0 := right_ne_zero_of_mul (show graphSource κ β η z ≠ 0 from hz)
  refine ⟨(z.re,z.im-κ z.re),⟨subset_tsupport _ hb,subset_tsupport _ he⟩,?_⟩
  apply Complex.ext <;> simp [graphChart]

lemma graphJump_compactSupport {κ β η : ℝ → ℝ} (hκ : Continuous κ)
    (hβ : HasCompactSupport β) (hη : HasCompactSupport η) :
    HasCompactSupport (graphJump κ β η) := by
  apply HasCompactSupport.of_support_subset_isCompact (graphSource_compactSupport hκ hβ hη)
  intro z hz
  apply subset_tsupport (graphSource κ β η)
  by_contra hn
  exact hz (by simp [graphJump,show graphSource κ β η z = 0 from not_ne_iff.mp hn])

lemma graphUpper_isOpen {κ : ℝ → ℝ} (hκ : Continuous κ) : IsOpen (graphUpper κ) :=
  isOpen_lt (hκ.comp Complex.continuous_re) Complex.continuous_im

lemma graphJump_eventuallyEq {κ β η : ℝ → ℝ} (hκ : Continuous κ) {A : Set ℂ}
    (hgraph : ∀ s ∈ tsupport β, graphChart κ s 0 ∈ A) {z : ℂ} (hz : z ∉ A) :
    (z ∈ graphUpper κ ∧ graphJump κ β η =ᶠ[𝓝 z] graphSource κ β η) ∨
    (z ∉ graphUpper κ ∧ graphJump κ β η =ᶠ[𝓝 z] 0 ∧
      gradient (graphJump κ β η) z = 0) := by
  by_cases hu : z ∈ graphUpper κ
  · refine Or.inl ⟨hu,?_⟩
    filter_upwards [(graphUpper_isOpen hκ).mem_nhds hu] with y hy
    exact indicator_of_mem hy _
  · have hzero : graphJump κ β η =ᶠ[𝓝 z] (0 : ℂ → ℝ) := by
      by_cases hl : z.im < κ z.re
      · filter_upwards [(isOpen_lt Complex.continuous_im (hκ.comp Complex.continuous_re)).mem_nhds hl] with y hy
        exact indicator_of_notMem (s := graphUpper κ) (fun hh => (not_lt_of_gt hy) hh) (graphSource κ β η)
      · have heq : z.im = κ z.re := le_antisymm (not_lt.mp hu) (not_lt.mp hl)
        have hzβ : z.re ∉ tsupport β := by
          intro hb
          apply hz
          have he : graphChart κ z.re 0 = z := by
            apply Complex.ext <;> simp [graphChart,heq]
          exact he ▸ hgraph z.re hb
        have hf : ∀ᶠ y in 𝓝 z, y.re ∉ tsupport β :=
          (isClosed_tsupport β).isOpen_compl.preimage Complex.continuous_re |>.mem_nhds hzβ
        filter_upwards [hf] with y hy
        simp [graphJump,graphSource,image_eq_zero_of_notMem_tsupport hy]
    refine Or.inr ⟨hu,hzero,?_⟩
    rw [Filter.EventuallyEq.gradient_eq hzero]
    exact gradient_fun_const z (0 : ℝ)

lemma graphJump_contDiffOn {κ β η : ℝ → ℝ} (hκ : ContDiff ℝ 1 κ)
    (hβ : ContDiff ℝ 1 β) (hη : ContDiff ℝ 1 η) {A : Set ℂ}
    (hgraph : ∀ s ∈ tsupport β, graphChart κ s 0 ∈ A) :
    ContDiffOn ℝ 1 (graphJump κ β η) Aᶜ := by
  intro z hz
  rcases graphJump_eventuallyEq hκ.continuous hgraph hz with ⟨_,he⟩ | ⟨_,he,_⟩
  · exact ((graphSource_contDiff hκ hβ hη).contDiffAt.congr_of_eventuallyEq he).contDiffWithinAt
  · exact (contDiffAt_const.congr_of_eventuallyEq he).contDiffWithinAt

lemma graphJump_gradient_eq {κ β η : ℝ → ℝ} (hκ : Continuous κ) {A : Set ℂ}
    (hgraph : ∀ s ∈ tsupport β, graphChart κ s 0 ∈ A) :
    EqOn (gradient (graphJump κ β η)) (graphJumpGradient κ β η) Aᶜ := by
  intro z hz
  rcases graphJump_eventuallyEq hκ hgraph hz with ⟨hu,he⟩ | ⟨hu,_,he⟩
  · simpa [graphJumpGradient,hu] using he.gradient_eq
  · simp [graphJumpGradient,hu,he]

lemma graphJump_sobolev {κ β η : ℝ → ℝ} (hκ : ContDiff ℝ 1 κ)
    (hβ : ContDiff ℝ 1 β) (hη : ContDiff ℝ 1 η)
    (hcβ : HasCompactSupport β) (hcη : HasCompactSupport η) {A : Set ℂ}
    (hA : IsClosed A) (hgraph : ∀ s ∈ tsupport β, graphChart κ s 0 ∈ A) :
    SobolevOn (graphJump κ β η) (graphJumpGradient κ β η) Aᶜ := by
  have hv := graphSource_contDiff hκ hβ hη
  have hc := graphSource_compactSupport hκ.continuous hcβ hcη
  have hvL : MemLp (graphSource κ β η) 2 volume := hv.continuous.memLp_of_hasCompactSupport hc
  have hgL : MemLp (gradient (graphSource κ β η)) 2 volume :=
    ((toDual ℝ ℂ).symm.continuous.comp (hv.continuous_fderiv (by norm_num))).memLp_of_hasCompactSupport
      ((hc.fderiv ℝ).comp_left (map_zero (toDual ℝ ℂ).symm))
  have hupper := (graphUpper_isOpen hκ.continuous).measurableSet
  have huL : MemLp (graphJump κ β η) 2 volume := hvL.indicator hupper
  have heL : MemLp (graphJumpGradient κ β η) 2 volume := hgL.indicator hupper
  have heq := graphJump_gradient_eq (η := η) hκ.continuous hgraph
  have hEq : gradient (graphJump κ β η) =ᵐ[volume.restrict Aᶜ] graphJumpGradient κ β η :=
    (ae_restrict_mem hA.isOpen_compl.measurableSet).mono fun x hx => heq hx
  have hs := sobolevOn_of_contDiffOn hA.isOpen_compl (graphJump_contDiffOn hκ hβ hη hgraph)
    (huL.restrict _) ((memLp_congr_ae hEq).mpr (heL.restrict _))
  refine ⟨hs.1,heL.restrict _,?_⟩
  intro ψ hψ hcψ htψ a
  rw [hs.2.2 ψ hψ hcψ htψ a]
  congr 1
  apply integral_congr_ae
  filter_upwards [hEq] with x hx
  rw [hx]

open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff

lemma graphSource_fderiv {κ β η : ℝ → ℝ} (hκ : ContDiff ℝ 1 κ)
    (hβ : ContDiff ℝ 1 β) (hη : ContDiff ℝ 1 η) (z a : ℂ) :
    fderiv ℝ (graphSource κ β η) z a =
      deriv β z.re * η (z.im-κ z.re) * a.re +
        β z.re * deriv η (z.im-κ z.re) * (a.im-deriv κ z.re*a.re) := by
  have hk := ((hκ.differentiable one_ne_zero z.re).hasDerivAt).comp_hasFDerivAt z Complex.reCLM.hasFDerivAt
  have hb := ((hβ.differentiable one_ne_zero z.re).hasDerivAt).comp_hasFDerivAt z Complex.reCLM.hasFDerivAt
  have hh := ((hη.differentiable one_ne_zero (z.im-κ z.re)).hasDerivAt).comp_hasFDerivAt z
    (Complex.imCLM.hasFDerivAt.sub hk)
  have h := (hb.mul hh).fderiv
  change fderiv ℝ (graphSource κ β η) z = _ at h
  rw [h]
  simp only [_root_.add_apply,_root_.smul_apply,_root_.sub_apply,
    Complex.reCLM_apply,Complex.imCLM_apply,smul_eq_mul,Function.comp_apply,Pi.sub_apply]
  ring

lemma graphChart_hasDerivAt_left {κ : ℝ → ℝ} (hκ : ContDiff ℝ 1 κ) (s r : ℝ) :
    HasDerivAt (fun s => graphChart κ s r) (1+Complex.ofReal (deriv κ s)*Complex.I) s := by
  have hi := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_id s)
  have hk := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt s
    ((hκ.differentiable one_ne_zero s).hasDerivAt.add_const r)
  change HasDerivAt (fun s : ℝ => Complex.ofReal s + Complex.ofReal (κ s+r)*Complex.I) _ s
  simpa only [Function.comp_def,id_eq,Pi.add_def,Complex.ofRealCLM_apply,Complex.ofReal_one] using hi.add (hk.mul_const Complex.I)

lemma graphChart_hasDerivAt_right (κ : ℝ → ℝ) (s r : ℝ) :
    HasDerivAt (graphChart κ s) Complex.I r := by
  have hk := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt r ((hasDerivAt_id r).const_add (κ s))
  change HasDerivAt (fun r => (s : ℂ) + Complex.ofReal (κ s+r)*Complex.I) _ r
  simpa only [Function.comp_def,id_eq,Pi.add_def,Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul] using (hk.mul_const Complex.I).const_add (s : ℂ)

def graphDS (κ β η : ℝ → ℝ) (G : ℂ → ℂ) (s r : ℝ) : ℝ :=
  deriv β s * η r * (G (graphChart κ s r)).re +
    β s * η r * (fderiv ℝ G (graphChart κ s r) (1+Complex.ofReal (deriv κ s)*Complex.I)).re

def graphDR (κ β η : ℝ → ℝ) (G : ℂ → ℂ) (s r : ℝ) : ℝ :=
  β s * deriv η r * ((G (graphChart κ s r)).im-deriv κ s*(G (graphChart κ s r)).re) +
    β s * η r * ((fderiv ℝ G (graphChart κ s r) Complex.I).im-
      deriv κ s*(fderiv ℝ G (graphChart κ s r) Complex.I).re)

lemma graphDS_hasDerivAt {κ β η : ℝ → ℝ} {G : ℂ → ℂ}
    (hκ : ContDiff ℝ 1 κ) (hβ : ContDiff ℝ 1 β) (hG : ContDiff ℝ 1 G) (s r : ℝ) :
    HasDerivAt (fun s => β s*η r*(G (graphChart κ s r)).re) (graphDS κ β η G s r) s := by
  have hGc := (hG.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt s (graphChart_hasDerivAt_left hκ s r)
  have hGr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hGc
  simpa [graphDS,mul_assoc,Function.comp_def,Pi.mul_def] using ((hβ.differentiable one_ne_zero s).hasDerivAt.mul_const (η r)).mul hGr

lemma graphDR_hasDerivAt {κ β η : ℝ → ℝ} {G : ℂ → ℂ}
    (hη : ContDiff ℝ 1 η) (hG : ContDiff ℝ 1 G) (s r : ℝ) :
    HasDerivAt (fun r => β s*η r*((G (graphChart κ s r)).im-deriv κ s*(G (graphChart κ s r)).re))
      (graphDR κ β η G s r) r := by
  have hGc := (hG.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt r (graphChart_hasDerivAt_right κ s r)
  have hGi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt r hGc
  have hGr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt r hGc
  simpa [graphDR,mul_assoc,Function.comp_def,Pi.mul_def,Pi.sub_def] using ((hη.differentiable one_ne_zero r).hasDerivAt.const_mul (β s)).mul
    (hGi.sub (hGr.const_mul (deriv κ s)))

lemma graphDS_add_graphDR {κ β η : ℝ → ℝ} {G : ℂ → ℂ}
    (hκ : ContDiff ℝ 1 κ) (hβ : ContDiff ℝ 1 β) (hη : ContDiff ℝ 1 η) (s r : ℝ) :
    graphDS κ β η G s r + graphDR κ β η G s r =
      inner ℝ (G (graphChart κ s r)) (gradient (graphSource κ β η) (graphChart κ s r)) +
        β s*η r*((fderiv ℝ G (graphChart κ s r) 1).re+(fderiv ℝ G (graphChart κ s r) Complex.I).im) := by
  rw [real_inner_comm,inner_gradient_left,graphSource_fderiv hκ hβ hη]
  have hlin : fderiv ℝ G (graphChart κ s r) (1+Complex.ofReal (deriv κ s)*Complex.I) =
      fderiv ℝ G (graphChart κ s r) 1 + deriv κ s • fderiv ℝ G (graphChart κ s r) Complex.I := by
    rw [show Complex.ofReal (deriv κ s)*Complex.I = deriv κ s • Complex.I from rfl,map_add,map_smul]
  simp only [graphDS,graphDR,hlin,Complex.add_re,Complex.smul_re,smul_eq_mul]
  simp only [graphChart,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
    Complex.ofReal_im,Complex.mul_im,Complex.I_im,Complex.add_im,mul_zero,sub_zero,add_zero,mul_one,zero_add]
  ring_nf

open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff

lemma graphDS_continuous {κ β η : ℝ → ℝ} {G : ℂ → ℂ}
    (hκ : ContDiff ℝ 1 κ) (hβ : ContDiff ℝ 1 β) (hη : Continuous η) (hG : ContDiff ℝ 1 G) :
    Continuous (fun p : ℝ × ℝ => graphDS κ β η G p.1 p.2) := by
  have hk' := hκ.continuous_deriv le_rfl
  have hb' := hβ.continuous_deriv le_rfl
  have hG' := hG.continuous_fderiv one_ne_zero
  have hk := hκ.continuous
  have hb := hβ.continuous
  have hg := hG.continuous
  unfold graphDS graphChart
  fun_prop

lemma graphDR_continuous {κ β η : ℝ → ℝ} {G : ℂ → ℂ}
    (hκ : ContDiff ℝ 1 κ) (hβ : Continuous β) (hη : ContDiff ℝ 1 η) (hG : ContDiff ℝ 1 G) :
    Continuous (fun p : ℝ × ℝ => graphDR κ β η G p.1 p.2) := by
  have hk' := hκ.continuous_deriv le_rfl
  have he' := hη.continuous_deriv le_rfl
  have hG' := hG.continuous_fderiv one_ne_zero
  have hk := hκ.continuous
  have he := hη.continuous
  have hg := hG.continuous
  unfold graphDR graphChart
  fun_prop

lemma graphDS_support {κ β η : ℝ → ℝ} {G : ℂ → ℂ} :
    Function.support (fun p : ℝ × ℝ => graphDS κ β η G p.1 p.2) ⊆ tsupport β ×ˢ tsupport η := by
  intro p hp
  constructor
  · by_contra hb
    exact hp (by simp [graphDS,image_eq_zero_of_notMem_tsupport hb,deriv_of_notMem_tsupport hb])
  · by_contra he
    exact hp (by simp [graphDS,image_eq_zero_of_notMem_tsupport he])

lemma graphDR_support {κ β η : ℝ → ℝ} {G : ℂ → ℂ} :
    Function.support (fun p : ℝ × ℝ => graphDR κ β η G p.1 p.2) ⊆ tsupport β ×ˢ tsupport η := by
  intro p hp
  constructor
  · by_contra hb
    exact hp (by simp [graphDR,image_eq_zero_of_notMem_tsupport hb])
  · by_contra he
    exact hp (by simp [graphDR,image_eq_zero_of_notMem_tsupport he,deriv_of_notMem_tsupport he])

lemma graphDS_integrable {κ β η : ℝ → ℝ} {G : ℂ → ℂ}
    (hκ : ContDiff ℝ 1 κ) (hβ : ContDiff ℝ 1 β) (hη : Continuous η) (hG : ContDiff ℝ 1 G)
    (hcβ : HasCompactSupport β) (hcη : HasCompactSupport η) :
    Integrable (fun p : ℝ × ℝ => graphDS κ β η G p.1 p.2) volume :=
  (graphDS_continuous hκ hβ hη hG).integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact (hcβ.isCompact.prod hcη.isCompact) graphDS_support)

lemma graphDR_integrable {κ β η : ℝ → ℝ} {G : ℂ → ℂ}
    (hκ : ContDiff ℝ 1 κ) (hβ : Continuous β) (hη : ContDiff ℝ 1 η) (hG : ContDiff ℝ 1 G)
    (hcβ : HasCompactSupport β) (hcη : HasCompactSupport η) :
    Integrable (fun p : ℝ × ℝ => graphDR κ β η G p.1 p.2) volume :=
  (graphDR_continuous hκ hβ hη hG).integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact (hcβ.isCompact.prod hcη.isCompact) graphDR_support)

lemma graphDS_integral_zero {κ β η : ℝ → ℝ} {G : ℂ → ℂ}
    (hκ : ContDiff ℝ 1 κ) (hβ : ContDiff ℝ 1 β) (hG : ContDiff ℝ 1 G)
    (hcβ : HasCompactSupport β) (r : ℝ) : (∫ s : ℝ, graphDS κ β η G s r) = 0 := by
  have hc : HasCompactSupport (fun s => β s*η r*(G (graphChart κ s r)).re) := (hcβ.mul_right).mul_right
  have ho : ContDiff ℝ 1 (fun s : ℝ => Complex.ofReal s) := Complex.ofRealCLM.contDiff
  have hr : ContDiff ℝ 1 (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have hf : ContDiff ℝ 1 (fun s => β s*η r*(G (graphChart κ s r)).re) := by
    unfold graphChart
    fun_prop
  have hd : (fun s => graphDS κ β η G s r) = deriv (fun s => β s*η r*(G (graphChart κ s r)).re) :=
    funext fun s => (graphDS_hasDerivAt hκ hβ hG s r).deriv.symm
  exact integral_eq_zero_of_hasDerivAt_of_integrable (fun s => graphDS_hasDerivAt hκ hβ hG s r)
    (hd ▸ (hf.continuous_deriv le_rfl).integrable_of_hasCompactSupport hc.deriv)
    (hf.continuous.integrable_of_hasCompactSupport hc)

lemma graphDR_integral_Ioi {κ β η : ℝ → ℝ} {G : ℂ → ℂ}
    (hη : ContDiff ℝ 1 η) (hG : ContDiff ℝ 1 G) (hcη : HasCompactSupport η) (s : ℝ) :
    (∫ r in Ioi (0:ℝ), graphDR κ β η G s r) =
      -(β s*η 0*((G (graphChart κ s 0)).im-deriv κ s*(G (graphChart κ s 0)).re)) := by
  let F := fun r => β s*η r*((G (graphChart κ s r)).im-deriv κ s*(G (graphChart κ s r)).re)
  have hc : HasCompactSupport F := (hcη.mul_left).mul_right
  have ho : ContDiff ℝ 1 (fun s : ℝ => Complex.ofReal s) := Complex.ofRealCLM.contDiff
  have hr : ContDiff ℝ 1 (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have hi : ContDiff ℝ 1 (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  have hf : ContDiff ℝ 1 F := by
    dsimp [F,graphChart]
    fun_prop
  have hd : (fun r => graphDR κ β η G s r) = deriv F :=
    funext fun r => (graphDR_hasDerivAt hη hG s r).deriv.symm
  rw [hd]
  exact HasCompactSupport.integral_Ioi_deriv_eq hf hc 0

end MumfordShah
end

end OAI
