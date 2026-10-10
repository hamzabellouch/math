import Mathlib
import OAI.Analysis.BiholderTransport.Volume.RadialNull
import OAI.Analysis.BiholderTransport.Regularity.TrialBlowup
import OAI.Analysis.BiholderTransport.LinearAlgebra.BranchHessian

namespace OAI

noncomputable section

namespace WeakMTWTransport

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Filter Set
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

section
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.contracted_segment_concaveOn (hmtw : WeakMTW (n := n) (M := M))
    {x : M} {p e xi : TangentSpace 𝓘(ℝ,Model n) x} {a b r : ℝ}
    (hseg : ∀ s ∈ Icc a b, p+s • e ∈ minimizingVectors x)
    (hr : 0<r) (hr1 : r<1) (hortho : inner ℝ xi e=0) :
    ConcaveOn ℝ (Icc a b) (fun s => hessianValue x (r • (p+s • e)) xi) := by
  have heq (s : ℝ) : r • p+s • (r • e)=r • (p+s • e) := by
    simp only [smul_add,smul_smul,mul_comm]
  have H := hmtw.transverse_concaveOn_injectivityDomain x (r • p) xi (r • e) (convex_Icc a b)
    (fun s hs => by rw [heq]; exact contracted_minimizer_mem_injectivityDomain (hseg s hs) hr hr1)
    (by simp only [real_inner_smul_right,hortho,mul_zero])
  simpa only [heq] using H

lemma WeakMTW.firstcut_transverse_lower (hmtw : WeakMTW (n := n) (M := M))
    {x : M} {p e xi : TangentSpace 𝓘(ℝ,Model n) x} {a b : ℝ}
    (ha : a<0) (hb : 0<b)
    (hseg : ∀ s ∈ Icc a b, p+s • e ∈ minimizingVectors x)
    (hleft : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x (p+a • e)) (riemannianExp x v)) (p+a • e)))
    (hright : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x (p+b • e)) (riemannianExp x v)) (p+b • e)))
    (hortho : inner ℝ xi e=0) :
    ∃ L : ℝ, ∀ᶠ r : ℝ in 𝓝[<] 1, ∀ s ∈ Icc a b,
      L≤hessianValue x (r • (p+s • e)) xi := by
  have hab : a≤b := (ha.trans hb).le
  obtain ⟨C,hC⟩ := nonconjugate_inward_hessian_bounded (hseg a ⟨le_rfl,hab⟩) hleft xi
  obtain ⟨D,hD⟩ := nonconjugate_inward_hessian_bounded (hseg b ⟨hab,le_rfl⟩) hright xi
  refine ⟨min (-C) (-D),?_⟩
  filter_upwards [hC,hD,
    (eventually_gt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with r hrC hrD hr0 hr1
  intro s hs
  have H := (hmtw.contracted_segment_concaveOn hseg hr0 hr1 hortho).min_le_of_mem_Icc
    (show a ∈ Icc a b from ⟨le_rfl,hab⟩) (show b ∈ Icc a b from ⟨hab,le_rfl⟩) hs
  exact (min_le_min (neg_le_of_abs_le hrC) (neg_le_of_abs_le hrD)).trans H

lemma WeakMTW.firstcut_kernel_transverse_orthogonal (hmtw : WeakMTW (n := n) (M := M))
    {x : M} {p e k : TangentSpace 𝓘(ℝ,Model n) x} {a b : ℝ}
    (ha : a<0) (hb : 0<b)
    (hseg : ∀ s ∈ Icc a b, p+s • e ∈ minimizingVectors x)
    (hleft : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x (p+a • e)) (riemannianExp x v)) (p+a • e)))
    (hright : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x (p+b • e)) (riemannianExp x v)) (p+b • e)))
    (hk : mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) (riemannianExp x) p k=0)
    (xi : TangentSpace 𝓘(ℝ,Model n) x) (hortho : inner ℝ xi e=0) : inner ℝ xi k=0 := by
  by_contra hpair
  have hp : p ∈ minimizingVectors x := by simpa using hseg 0 ⟨ha.le,hb.le⟩
  have hneg := conjugate_radial_hessian_tendsto_atBot hp hk
    (by rwa [real_inner_comm] : inner ℝ k xi≠0)
  obtain ⟨L,hL⟩ := hmtw.firstcut_transverse_lower ha hb hseg hleft hright hortho
  have hlo : ∀ᶠ r : ℝ in 𝓝[<] 1, L≤hessianValue x (r • p) xi :=
    hL.mono (fun r hr => by simpa using hr 0 ⟨ha.le,hb.le⟩)
  obtain ⟨r,hr,hrr⟩ := (hlo.and (hneg.eventually (eventually_lt_atBot L))).exists
  exact (not_lt_of_ge hr) hrr
end

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.firstcut_radial_lower (hmtw : WeakMTW (n := n) (M := M))
    {x : M} {p e : TangentSpace 𝓘(ℝ,Model n) x} {b : ℝ}
    (hb : 0<b) (hseg : ∀ s ∈ Icc 0 b, p+s • e ∈ minimizingVectors x)
    (hright : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x (p+b • e)) (riemannianExp x v)) (p+b • e)))
    (hortho : inner ℝ p e=0) :
    ∃ D : ℝ, ∀ᶠ r : ℝ in 𝓝[<] 1, ∀ s ∈ Icc 0 b,
      -D * s ≤ s^2 * hessianValue x (r • (p+s • e)) e := by
  have hp : p ∈ minimizingVectors x := by simpa using hseg 0 ⟨le_rfl,hb.le⟩
  obtain ⟨C,hC⟩ := nonconjugate_inward_hessian_bounded (hseg b ⟨hb.le,le_rfl⟩) hright p
  let D := (C+‖p‖^2)/b
  refine ⟨D,?_⟩
  filter_upwards [hC,
    (eventually_gt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with r hrC hr0 hr1
  have hconc := hmtw.contracted_segment_concaveOn hseg hr0 hr1 hortho
  have hconv := hconc.neg.add_const (‖p‖^2)
  have hrad0 := hessianValue_contracted_radial hr0.ne'
    (contracted_minimizer_mem_injectivityDomain hp hr0 hr1)
  have hz : -hessianValue x (r • (p+(0:ℝ) • e)) p+‖p‖^2=0 := by
    simp only [zero_smul,add_zero,hrad0,neg_add_cancel]
  have hend : -hessianValue x (r • (p+b • e)) p+‖p‖^2≤D*b := by
    have hd : D*b=C+‖p‖^2 := div_mul_cancel₀ _ hb.ne'
    rw [hd]
    linarith [neg_le_of_abs_le hrC]
  intro s hs
  have hlin := convex_linear_bound hb hconv hz hend hs
  have hrad := hessianValue_transverse_radial_identity hr0.ne'
    (contracted_minimizer_mem_injectivityDomain (hseg s hs) hr0 hr1) hortho
  dsimp only [Pi.neg_apply,Pi.add_apply] at hlin
  nlinarith [mul_nonneg (sq_nonneg s) (sq_nonneg ‖e‖)]

end WeakMTWTransport

end

end OAI
