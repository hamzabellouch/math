import Mathlib
import OAI.Analysis.MumfordShah.LocalFlux
import OAI.Analysis.MumfordShah.ArcGraphs

namespace OAI

/-! MumfordShah rotation rigidity. -/

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
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open Laplacian ContinuousLinearMap
open scoped ENNReal NNReal ContDiff
open Set Metric Topology InnerProductSpace Complex MeasureTheory
open scoped ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff

open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap

open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff

lemma SobolevOn.comp_linearIsometry {u : ℂ → ℝ} {m : ℂ → ℂ} {U : Set ℂ}
    (hu : SobolevOn u m U) (hU : MeasurableSet U) (R : ℂ ≃ₗᵢ[ℝ] ℂ) :
    SobolevOn (fun x => u (R x)) (fun x => R.symm (m (R x))) (R ⁻¹' U) := by
  have hp := R.measurePreserving.restrict_preimage hU
  refine ⟨hu.1.comp_measurePreserving hp,?_,?_⟩
  · exact (hu.2.1.comp_measurePreserving hp).continuousLinearMap_comp
      R.symm.toContinuousLinearEquiv.toContinuousLinearMap
  intro ψ hψ hc ht a
  let Ψ := fun x : ℂ => ψ (R.symm x)
  have hΨ : ContDiff ℝ ∞ Ψ := hψ.comp R.symm.toContinuousLinearEquiv.contDiff
  have hcΨ : HasCompactSupport Ψ := hc.comp_homeomorph R.symm.toHomeomorph
  have hsΨ : tsupport Ψ ⊆ U := by
    intro x hx
    have hh := ht (tsupport_comp_subset_preimage ψ R.symm.continuous hx)
    simpa only [mem_preimage,R.apply_symm_apply] using hh
  have hh := hu.2.2 Ψ hΨ hcΨ hsΨ (R a)
  have hl := hp.integral_comp R.toHomeomorph.measurableEmbedding
    (fun x => u x * fderiv ℝ Ψ x (R a))
  have hr := hp.integral_comp R.toHomeomorph.measurableEmbedding
    (fun x => inner ℝ (m x) (R a) * Ψ x)
  have hd (x : ℂ) : fderiv ℝ Ψ (R x) (R a) = fderiv ℝ ψ x a := by
    rw [show Ψ = ψ ∘ R.symm from rfl,
      fderiv_comp (R x) (hψ.differentiable (by norm_num) _) R.symm.differentiableAt]
    have hrd : HasFDerivAt (fun y => R.symm y) R.symm.toContinuousLinearEquiv.toContinuousLinearMap (R x) := R.symm.toContinuousLinearEquiv.hasFDerivAt
    rw [hrd.fderiv]
    simp
  have hi (x : ℂ) : inner ℝ (m x) (R a) = inner ℝ (R.symm (m x)) a := by
    rw [← R.inner_map_map (R.symm (m x)) a,R.apply_symm_apply]
  simp only [hd] at hl
  simp only [Ψ,R.symm_apply_apply,hi] at hr
  rw [hl,hr]
  simpa only [Ψ,hi] using hh

lemma essentialSupport_comp_linearIsometry (u : ℂ → ℝ) (R : ℂ ≃ₗᵢ[ℝ] ℂ) :
    essentialSupport (fun x => u (R x)) = R ⁻¹' essentialSupport u := by
  ext x
  unfold essentialSupport
  simp only [mem_ofPred_eq,mem_preimage]
  have hp (r : ℝ) : MeasurePreserving R (volume.restrict (ball x r))
      (volume.restrict (ball (R x) r)) := by
    have hpre : R ⁻¹' ball (R x) r = ball x r := by
      ext y
      simp only [mem_preimage,mem_ball,R.dist_map]
    simpa only [hpre] using R.measurePreserving.restrict_preimage (measurableSet_ball (x := R x) (ε := r))
  have hae (r : ℝ) : (∀ᵐ y ∂volume.restrict (ball x r), u (R y) = 0) ↔
      ∀ᵐ y ∂volume.restrict (ball (R x) r), u y = 0 := by
    have hmb : MeasurableEmbedding (R : ℂ → ℂ) := R.toHomeomorph.measurableEmbedding
    rw [← (hp r).map_eq, hmb.ae_map_iff]
  simp only [hae]

lemma harmonicAt_comp_rotation {f : ℂ → ℝ} (a : Circle) {z : ℂ}
    (hf : HarmonicAt f (_root_.rotation a z)) :
    HarmonicAt (fun w => f (_root_.rotation a w)) z := by
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp (isOpen_setOfPred_harmonicAt (f := f)) _ hf
  obtain ⟨F,hF,hre⟩ := (show HarmonicOnNhd f (ball (_root_.rotation a z) r) from fun x hx => hball hx).exists_analyticOnNhd_ball_re_eq
  have hrot : AnalyticAt ℂ (fun w : ℂ => _root_.rotation a w) z := by
    simp only [_root_.rotation_apply]
    exact analyticAt_const.mul analyticAt_id
  have hh : HarmonicAt (fun w => (F (_root_.rotation a w)).re) z :=
    ((hF _ (mem_ball_self hr)).comp hrot).harmonicAt_re
  apply (harmonicAt_congr_nhds _).mp hh
  filter_upwards [(_root_.rotation a).continuous.continuousAt.eventually
    (ball_mem_nhds (_root_.rotation a z) hr)] with w hw
  exact hre hw

open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff

lemma gradient_comp_linearIsometry {f : ℂ → ℝ} (R : ℂ ≃ₗᵢ[ℝ] ℂ) {x : ℂ}
    (hf : DifferentiableAt ℝ f (R x)) :
    gradient (fun y => f (R y)) x = R.symm (gradient f (R x)) := by
  apply ext_inner_right ℝ
  intro y
  rw [inner_gradient_left, ← R.inner_map_map (R.symm (gradient f (R x))) y,
    R.apply_symm_apply,inner_gradient_left]
  have hh := hf.hasFDerivAt.comp x R.toContinuousLinearEquiv.hasFDerivAt
  change (fderiv ℝ (f ∘ R) x) y = _
  rw [hh.fderiv]
  rfl

lemma constant_jump_interactions_comp_linearIsometry {A : Set ℂ} (hA : IsClosed A)
    {G : ℂ → ℂ} {δ : ℝ}
    (hints : ∀ k : ℂ → ℝ, ∀ d : ℂ → ℂ, SobolevOn k d Aᶜ →
      IsCompact (essentialSupport k) → ∀ t ∈ ball (0:ℂ) δ,
      (∫ z : ℂ, inner ℝ (G z) (d (z-t))) = ∫ z : ℂ, inner ℝ (G z) (d z))
    (R : ℂ ≃ₗᵢ[ℝ] ℂ) :
    ∀ k : ℂ → ℝ, ∀ d : ℂ → ℂ, SobolevOn k d (R ⁻¹' A)ᶜ →
      IsCompact (essentialSupport k) → ∀ t ∈ ball (0:ℂ) δ,
      (∫ z : ℂ, inner ℝ (R.symm (G (R z))) (d (z-t))) =
        ∫ z : ℂ, inner ℝ (R.symm (G (R z))) (d z) := by
  intro k d hkd hkc t ht
  have hsob := hkd.comp_linearIsometry (hA.preimage R.continuous).measurableSet.compl R.symm
  have hpre : R.symm ⁻¹' (R ⁻¹' A)ᶜ = Aᶜ := by
    ext z; simp only [mem_preimage,mem_compl_iff,R.apply_symm_apply]
  rw [hpre] at hsob
  have hc : IsCompact (essentialSupport (fun z => k (R.symm z))) := by
    rw [essentialSupport_comp_linearIsometry]
    exact R.symm.toHomeomorph.isCompact_preimage.mpr hkc
  have hRt : R t ∈ ball (0:ℂ) δ := by simpa only [mem_ball,dist_zero_right,R.norm_map] using ht
  have he := hints _ _ hsob hc (R t) hRt
  have hl := R.measurePreserving.integral_comp R.toHomeomorph.measurableEmbedding
    (fun z => inner ℝ (G z) (R (d (R.symm (z-R t)))))
  have hr := R.measurePreserving.integral_comp R.toHomeomorph.measurableEmbedding
    (fun z => inner ℝ (G z) (R (d (R.symm z))))
  have hi (z w : ℂ) : inner ℝ (G (R z)) (R w) = inner ℝ (R.symm (G (R z))) w := by
    rw [← R.inner_map_map (R.symm (G (R z))) w,R.apply_symm_apply]
  simp only [map_sub,R.symm_apply_apply,hi] at hl hr
  rw [hl,hr]
  simpa only [R.symm_symm,map_sub,R.symm_apply_apply] using he

open Set MeasureTheory Metric Topology Filter InnerProductSpace
open Laplacian ContinuousLinearMap
open scoped ENNReal NNReal ContDiff

theorem harmonic_affine_of_arc_jump_interactions {A H O : Set ℂ}
    (hA : IsClosed A) (hO : IsOpen O) (hOc : IsConnected O) (hAO : A ⊆ O)
    (hArc : ContainsOpenC1Arc A H) {f : ℂ → ℝ} (hf : HarmonicOnNhd f O)
    {G : ℂ → ℂ} (hGeq : ∀ᵐ z ∂volume, z ∈ O → G z = gradient f z)
    {r : ℝ} (hr : 0 < r)
    (hints : ∀ k : ℂ → ℝ, ∀ d : ℂ → ℂ, SobolevOn k d Aᶜ →
      IsCompact (essentialSupport k) → ∀ t ∈ ball (0:ℂ) r,
      (∫ z : ℂ, inner ℝ (G z) (d (z-t))) = ∫ z : ℂ, inner ℝ (G z) (d z)) :
    ∃ L : ℂ →L[ℝ] ℝ, ∃ b : ℝ, ∀ z ∈ O, f z = L z+b := by
  obtain ⟨a,κ,hκ,I,hI,s₀,hs₀,hgraph⟩ := containsOpenC1Arc_rotated_graph hArc
  let R := _root_.rotation a
  let O' := R ⁻¹' O
  let A' := R ⁻¹' A
  have hO' : IsOpen O' := hO.preimage R.continuous
  have hOc' : IsConnected O' := R.toHomeomorph.isConnected_preimage.mpr hOc
  have hA' : IsClosed A' := hA.preimage R.continuous
  have hAO' : A' ⊆ O' := preimage_mono hAO
  have hf' : HarmonicOnNhd (fun z => f (R z)) O' := by
    intro z hz
    exact harmonicAt_comp_rotation a (hf _ hz)
  let G' := fun z => R.symm (G (R z))
  have hg' : ∀ᵐ z ∂volume, z ∈ O' → G' z = gradient (fun z => f (R z)) z := by
    filter_upwards [R.measurePreserving.quasiMeasurePreserving.ae hGeq] with z hz
    intro hzo
    dsimp only [G']
    rw [hz hzo,gradient_comp_linearIsometry R ((hf _ hzo).1.differentiableAt (by norm_num))]
  obtain ⟨J,hJ,hsJ,hJI,η,hη,hcη,hη0,δ,hδ,hδr,hstrip⟩ :=
    graph_strip_inside_open hO' hAO' hκ hI hs₀ hgraph hr
  have htests := constant_jump_interactions_comp_linearIsometry hA hints R
  obtain ⟨L,b,haff⟩ := harmonic_affine_of_compact_jump_interactions hA' hO' hOc' hf' hg'
    hκ hη hcη hη0 hJ hsJ (fun s hs => hgraph s (hJI hs)) hδ hstrip
    (fun k d hkd hkc t ht => htests k d hkd hkc t (ball_subset_ball hδr ht))
  refine ⟨L.comp R.symm.toContinuousLinearEquiv.toContinuousLinearMap,b,?_⟩
  intro z hz
  have hz' : R.symm z ∈ O' := by simpa only [O',mem_preimage,R.apply_symm_apply] using hz
  simpa only [R.apply_symm_apply,ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,ContinuousLinearEquiv.coe_coe] using haff _ hz'

end MumfordShah
end

end OAI
