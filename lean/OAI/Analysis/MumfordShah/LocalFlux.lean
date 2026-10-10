import Mathlib
import OAI.Analysis.MumfordShah.JumpInteraction
import OAI.Analysis.MumfordShah.GraphFlux

namespace OAI

/-! MumfordShah local flux. -/

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
open Set MeasureTheory Metric Topology InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff

open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap

open Set MeasureTheory Metric Topology Filter
open scoped ContDiff

lemma gradient_contDiffAt_of_two {f : ℂ → ℝ} {z : ℂ} (hf : ContDiffAt ℝ 2 f z) :
    ContDiffAt ℝ 1 (gradient f) z := by
  exact (toDual ℝ ℂ).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp z
    (hf.fderiv_right (by norm_num))

lemma riesz_re (L : ℂ →L[ℝ] ℝ) : ((toDual ℝ ℂ).symm L).re = L 1 := by
  simpa only [Complex.inner,one_mul,Complex.conj_re] using (toDual_symm_apply (𝕜 := ℝ) (x := (1:ℂ)) (y := L))

lemma riesz_im (L : ℂ →L[ℝ] ℝ) : ((toDual ℝ ℂ).symm L).im = L Complex.I := by
  simpa only [Complex.inner,Complex.mul_re,Complex.I_re,Complex.I_im,Complex.conj_re,Complex.conj_im,zero_mul,one_mul,zero_sub,neg_neg] using (toDual_symm_apply (𝕜 := ℝ) (x := Complex.I) (y := L))

lemma gradient_divergence_eq_laplacian {f : ℂ → ℝ} {z : ℂ} (hf : ContDiffAt ℝ 2 f z) :
    (fderiv ℝ (gradient f) z 1).re + (fderiv ℝ (gradient f) z Complex.I).im = Δ f z := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have he := (toDual ℝ ℂ).symm.toContinuousLinearEquiv.hasFDerivAt.comp z hd.hasFDerivAt
  have he' : fderiv ℝ (gradient f) z =
      (toDual ℝ ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ f) z) := he.fderiv
  rw [he']
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,riesz_re,riesz_im,
    laplacian_eq_iteratedFDeriv_complexPlane,iteratedFDeriv_two_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]

lemma harmonic_gradient_divergence {f : ℂ → ℝ} {z : ℂ} (hf : HarmonicAt f z) :
    (fderiv ℝ (gradient f) z 1).re + (fderiv ℝ (gradient f) z Complex.I).im = 0 := by
  rw [gradient_divergence_eq_laplacian hf.1]
  exact hf.2.eq_of_nhds

lemma contDiffAt_compact_extension {K O : Set ℂ} (hK : IsCompact K) (hO : IsOpen O)
    (hKO : K ⊆ O) {F : ℂ → ℂ} (hF : ∀ z ∈ O, ContDiffAt ℝ 1 F z) :
    ∃ G : ℂ → ℂ, ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
      ∀ z ∈ K, G =ᶠ[𝓝 z] F := by
  obtain ⟨χ,hχ,hχc,hχt,hχ1,_⟩ := compact_smooth_cutoff hK hO hKO
  let G := fun z => χ z • F z
  refine ⟨G,?_,?_,?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ O
    · exact ((hχ.of_le (by simp)).contDiffAt).smul (hF z hz)
    · have hn : z ∉ tsupport χ := fun hh => hz (hχt hh)
      have he : G =ᶠ[𝓝 z] (0 : ℂ → ℂ) := by
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hn] with y hy
        simp only [G,image_eq_zero_of_notMem_tsupport hy,zero_smul,Pi.zero_apply]
      exact contDiffAt_const.congr_of_eventuallyEq he
  · exact hχc.smul_right
  · intro z hz
    filter_upwards [hχ1 z hz] with y hy
    simp only [G,hy,Pi.one_apply,one_smul]

lemma harmonic_gradient_compact_extension {K O : Set ℂ} (hK : IsCompact K) (hO : IsOpen O)
    (hKO : K ⊆ O) {f : ℂ → ℝ} (hf : HarmonicOnNhd f O) :
    ∃ G : ℂ → ℂ, ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
      ∀ z ∈ K, G =ᶠ[𝓝 z] gradient f :=
  contDiffAt_compact_extension hK hO hKO (fun z hz => gradient_contDiffAt_of_two (hf z hz).1)

open Set MeasureTheory Metric Topology Filter InnerProductSpace
open Laplacian ContinuousLinearMap
open scoped ENNReal NNReal ContDiff

def graphTube (κ β η : ℝ → ℝ) : Set ℂ :=
  (fun p : ℝ × ℝ => graphChart κ p.1 p.2) '' (tsupport β ×ˢ tsupport η)

lemma graphTube_isCompact {κ β η : ℝ → ℝ} (hκ : Continuous κ)
    (hcβ : HasCompactSupport β) (hcη : HasCompactSupport η) : IsCompact (graphTube κ β η) := by
  apply (hcβ.isCompact.prod hcη.isCompact).image
  unfold graphChart
  fun_prop

lemma graphSource_tsupport_subset {κ β η : ℝ → ℝ} (hκ : Continuous κ)
    (hcβ : HasCompactSupport β) (hcη : HasCompactSupport η) :
    tsupport (graphSource κ β η) ⊆ graphTube κ β η := by
  apply closure_minimal _ (graphTube_isCompact hκ hcβ hcη).isClosed
  intro z hz
  have hb : β z.re ≠ 0 := left_ne_zero_of_mul (show graphSource κ β η z ≠ 0 from hz)
  have he : η (z.im-κ z.re) ≠ 0 := right_ne_zero_of_mul (show graphSource κ β η z ≠ 0 from hz)
  refine ⟨(z.re,z.im-κ z.re),⟨subset_tsupport _ hb,subset_tsupport _ he⟩,?_⟩
  apply Complex.ext <;> simp [graphChart]

lemma graphJumpGradient_zero_off_tube {κ β η : ℝ → ℝ} (hκ : Continuous κ)
    (hcβ : HasCompactSupport β) (hcη : HasCompactSupport η) {z : ℂ}
    (hz : z ∉ graphTube κ β η) : graphJumpGradient κ β η z = 0 := by
  have hv : z ∉ tsupport (graphSource κ β η) := fun hh => hz (graphSource_tsupport_subset hκ hcβ hcη hh)
  have hg : gradient (graphSource κ β η) z = 0 := by
    simp only [gradient,fderiv_of_notMem_tsupport ℝ hv,map_zero]
  by_cases hu : z ∈ graphUpper κ <;> simp [graphJumpGradient,hu,hg]

lemma local_graph_jump_flux {κ β η : ℝ → ℝ} {F : ℂ → ℂ} {O : Set ℂ}
    (hκ : ContDiff ℝ 1 κ) (hβ : ContDiff ℝ 1 β) (hη : ContDiff ℝ 1 η)
    (hcβ : HasCompactSupport β) (hcη : HasCompactSupport η) (hη0 : η 0 = 1)
    (hO : IsOpen O) (htube : graphTube κ β η ⊆ O)
    (hF : ∀ z ∈ O, ContDiffAt ℝ 1 F z)
    (hdiv : ∀ z ∈ O, (fderiv ℝ F z 1).re+(fderiv ℝ F z Complex.I).im = 0) :
    (∫ z : ℂ, inner ℝ (F z) (graphJumpGradient κ β η z)) =
      -(∫ s : ℝ, β s * ((F (graphChart κ s 0)).im - deriv κ s*(F (graphChart κ s 0)).re)) := by
  obtain ⟨G,hG,_,hGeq⟩ := contDiffAt_compact_extension
    (graphTube_isCompact hκ.continuous hcβ hcη) hO htube hF
  have h0 : (0:ℝ) ∈ tsupport η := subset_tsupport _ (by simp [hη0])
  have he : (∫ z : ℂ, inner ℝ (F z) (graphJumpGradient κ β η z)) =
      (∫ z : ℂ, inner ℝ (G z) (graphJumpGradient κ β η z)) := by
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hz : z ∈ graphTube κ β η
    · rw [(hGeq z hz).eq_of_nhds]
    · simp only [graphJumpGradient_zero_off_tube hκ.continuous hcβ hcη hz,inner_zero_right]
  rw [he,graph_jump_flux hκ hβ hη hcβ hcη hG (by
    intro s hs r hr
    have hz : graphChart κ s r ∈ graphTube κ β η := ⟨(s,r),⟨hs,hr⟩,rfl⟩
    rw [(hGeq _ hz).fderiv_eq]
    exact hdiv _ (htube hz))]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with s
  by_cases hs : s ∈ tsupport β
  · rw [(hGeq _ ⟨(s,0),⟨hs,h0⟩,rfl⟩).eq_of_nhds,hη0,mul_one]
  · simp only [image_eq_zero_of_notMem_tsupport hs,zero_mul]

lemma harmonic_graph_jump_flux {κ β η : ℝ → ℝ} {f : ℂ → ℝ} {O : Set ℂ}
    (hκ : ContDiff ℝ 1 κ) (hβ : ContDiff ℝ 1 β) (hη : ContDiff ℝ 1 η)
    (hcβ : HasCompactSupport β) (hcη : HasCompactSupport η) (hη0 : η 0 = 1)
    (hO : IsOpen O) (hf : HarmonicOnNhd f O) (t : ℂ)
    (htube : ∀ z ∈ graphTube κ β η, z+t ∈ O) :
    (∫ z : ℂ, inner ℝ (gradient f (z+t)) (graphJumpGradient κ β η z)) =
      -(∫ s : ℝ, β s * fderiv ℝ f (graphChart κ s 0+t)
        (Complex.I-Complex.ofReal (deriv κ s))) := by
  have hh := local_graph_jump_flux (F := fun z => gradient f (z+t))
    hκ hβ hη hcβ hcη hη0 (hO.preimage (continuous_id.add continuous_const)) htube
    (fun z hz => (gradient_contDiffAt_of_two (hf _ hz).1).comp z (contDiffAt_id.add contDiffAt_const)) (by
      intro z hz
      rw [fderiv_comp_add_right]
      exact harmonic_gradient_divergence (hf _ hz))
  rw [hh]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with s
  rw [map_sub,show Complex.ofReal (deriv κ s) = deriv κ s • (1:ℂ) from by simp,map_smul]
  simp only [gradient,riesz_re,riesz_im,smul_eq_mul]

open Set Metric Topology InnerProductSpace Complex MeasureTheory
open scoped ContDiff

lemma graph_jump_interaction_eq_flux {κ β η : ℝ → ℝ} {f : ℂ → ℝ} {G : ℂ → ℂ} {O : Set ℂ}
    (hκ : ContDiff ℝ 1 κ) (hβ : ContDiff ℝ 1 β) (hη : ContDiff ℝ 1 η)
    (hcβ : HasCompactSupport β) (hcη : HasCompactSupport η) (hη0 : η 0 = 1)
    (hO : IsOpen O) (hf : HarmonicOnNhd f O)
    (hGeq : ∀ᵐ z ∂volume, z ∈ O → G z = gradient f z) (t : ℂ)
    (htube : ∀ z ∈ graphTube κ β η, z+t ∈ O) :
    (∫ z : ℂ, inner ℝ (G z) (graphJumpGradient κ β η (z-t))) =
      -(∫ s : ℝ, β s * fderiv ℝ f (graphChart κ s 0+t)
        (Complex.I-Complex.ofReal (deriv κ s))) := by
  rw [← (measurePreserving_add_right (volume : Measure ℂ) t).integral_comp
    (Homeomorph.addRight t).measurableEmbedding]
  simp only [add_sub_cancel_right]
  rw [← harmonic_graph_jump_flux hκ hβ hη hcβ hcη hη0 hO hf t htube]
  apply integral_congr_ae
  have hae := (measurePreserving_add_right (volume : Measure ℂ) t).quasiMeasurePreserving.ae hGeq
  filter_upwards [hae] with z hz
  by_cases ht : z ∈ graphTube κ β η
  · rw [hz (htube z ht)]
  · simp only [graphJumpGradient_zero_off_tube hκ.continuous hcβ hcη ht,inner_zero_right]

lemma graph_flux_integrable {κ β : ℝ → ℝ} {f : ℂ → ℝ} {O : Set ℂ} {I : Set ℝ}
    (hκ : ContDiff ℝ 1 κ) (hβ : Continuous β) (hcβ : HasCompactSupport β)
    (hβI : tsupport β ⊆ I) (_hI : IsOpen I) (hf : HarmonicOnNhd f O) (t : ℂ)
    (hplace : ∀ s ∈ I, graphChart κ s 0+t ∈ O) :
    Integrable (fun s => β s * fderiv ℝ f (graphChart κ s 0+t)
      (Complex.I-Complex.ofReal (deriv κ s))) volume := by
  apply Continuous.integrable_of_hasCompactSupport _ hcβ.mul_right
  rw [continuous_iff_continuousAt]
  intro s
  by_cases hs : s ∈ I
  · have hg : ContinuousAt (fderiv ℝ f) (graphChart κ s 0+t) :=
      ((hf _ (hplace s hs)).1.fderiv_right (m := 1) (by norm_num)).continuousAt
    have hk := hκ.continuous
    have hk' := hκ.continuous_deriv le_rfl
    have hc : Continuous (fun s => graphChart κ s 0+t) := by unfold graphChart; fun_prop
    have hn : Continuous (fun s => Complex.I-Complex.ofReal (deriv κ s)) := by fun_prop
    exact hβ.continuousAt.mul ((hg.comp (f := fun s : ℝ => graphChart κ s 0+t) hc.continuousAt).clm_apply hn.continuousAt)
  · have hn : s ∉ tsupport β := fun hh => hs (hβI hh)
    have he : (fun s => β s*fderiv ℝ f (graphChart κ s 0+t)
        (Complex.I-Complex.ofReal (deriv κ s))) =ᶠ[𝓝 s] 0 := by
      filter_upwards [(isClosed_tsupport β).isOpen_compl.mem_nhds hn] with r hr
      simp only [image_eq_zero_of_notMem_tsupport hr,zero_mul,Pi.zero_apply]
    exact continuousAt_const.congr he.symm

theorem harmonic_affine_of_compact_jump_interactions
    {A O : Set ℂ} (hA : IsClosed A) (hO : IsOpen O) (hOc : IsConnected O)
    {f : ℂ → ℝ} (hf : HarmonicOnNhd f O) {G : ℂ → ℂ}
    (hGeq : ∀ᵐ z ∂volume, z ∈ O → G z = gradient f z)
    {κ η : ℝ → ℝ} (hκ : ContDiff ℝ 1 κ) (hη : ContDiff ℝ 1 η)
    (hcη : HasCompactSupport η) (hη0 : η 0 = 1)
    {I : Set ℝ} (hI : IsOpen I) {s₀ : ℝ} (hs₀ : s₀ ∈ I)
    (hgraph : ∀ s ∈ I, graphChart κ s 0 ∈ A)
    {δ : ℝ} (hδ : 0 < δ)
    (hstrip : ∀ s ∈ I, ∀ r ∈ tsupport η, ∀ t ∈ ball (0:ℂ) δ, graphChart κ s r+t ∈ O)
    (hints : ∀ k : ℂ → ℝ, ∀ d : ℂ → ℂ, SobolevOn k d Aᶜ →
      IsCompact (essentialSupport k) → ∀ t ∈ ball (0:ℂ) δ,
      (∫ z : ℂ, inner ℝ (G z) (d (z-t))) = ∫ z : ℂ, inner ℝ (G z) (d z)) :
    ∃ L : ℂ →L[ℝ] ℝ, ∃ b : ℝ, ∀ z ∈ O, f z = L z+b := by
  have h0 : (0:ℝ) ∈ tsupport η := subset_tsupport _ (by simp [hη0])
  have hk := hκ.continuous
  have hk' := hκ.continuous_deriv le_rfl
  have hγ : Continuous (fun s => graphChart κ s 0) := by unfold graphChart; fun_prop
  have hn : Continuous (fun s => Complex.I-Complex.ofReal (deriv κ s)) := by fun_prop
  apply harmonic_affine_of_jump_tests hO hOc hf hI hs₀ hγ.continuousOn hn.continuousOn
    (w := fun _ => 1) continuousOn_const (by
      intro he
      have hi := congrArg Complex.im he
      simp at hi) (by norm_num) hδ (fun s hs t ht => hstrip s hs 0 h0 t ht)
  intro t ht β hβ hcβ hβI
  have hβ1 : ContDiff ℝ 1 β := hβ.of_le (by norm_num)
  have hsob := graphJump_sobolev hκ hβ1 hη hcβ hcη hA (fun s hs => hgraph s (hβI hs))
  have hcomp : IsCompact (essentialSupport (graphJump κ β η)) :=
    (graphJump_compactSupport hκ.continuous hcβ hcη).isCompact.of_isClosed_subset
      (isClosed_essentialSupport _) (essentialSupport_subset_tsupport _)
  have hf0 := graph_jump_interaction_eq_flux hκ hβ1 hη hcβ hcη hη0 hO hf hGeq (0:ℂ) (by
    rintro z ⟨⟨s,r⟩,⟨hs,hr⟩,rfl⟩
    exact hstrip s (hβI hs) r hr 0 (mem_ball_self hδ))
  have hft := graph_jump_interaction_eq_flux hκ hβ1 hη hcβ hcη hη0 hO hf hGeq t (by
    rintro z ⟨⟨s,r⟩,⟨hs,hr⟩,rfl⟩
    exact hstrip s (hβI hs) r hr t ht)
  have he := hints _ _ hsob hcomp t ht
  simp only [sub_zero,add_zero] at hf0
  rw [hft,hf0] at he
  have hz : (∫ s : ℝ, β s * fderiv ℝ f (graphChart κ s 0+t) (Complex.I-Complex.ofReal (deriv κ s))) =
      ∫ s : ℝ, β s * fderiv ℝ f (graphChart κ s 0) (Complex.I-Complex.ofReal (deriv κ s)) := neg_injective he
  have htint := graph_flux_integrable hκ hβ.continuous hcβ hβI hI hf t
    (fun s hs => hstrip s hs 0 h0 t ht)
  have h0int := graph_flux_integrable hκ hβ.continuous hcβ hβI hI hf (0:ℂ)
    (fun s hs => hstrip s hs 0 h0 0 (mem_ball_self hδ))
  simp only [add_zero] at h0int
  simp only [mul_one,mul_sub]
  rw [integral_sub htint h0int,hz,sub_self]

end MumfordShah
end

end OAI
