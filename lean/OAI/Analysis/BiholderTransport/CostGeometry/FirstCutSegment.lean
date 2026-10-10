import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.CurvedBlowup
import OAI.Analysis.BiholderTransport.CostGeometry.FirstCutLower
import OAI.Analysis.BiholderTransport.Coordinates.KernelRadial

namespace OAI

noncomputable section

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

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma kernel_parallel_of_transverse_orthogonal_ne_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {e k : E} (he : e ≠ 0)
    (hk : ∀ xi : E, inner ℝ xi e=0 → inner ℝ xi k=0) :
    k=(inner ℝ k e / inner ℝ e e) • e := by
  have hee : inner ℝ e e ≠ 0 := inner_self_ne_zero.mpr he
  let xi := k-(inner ℝ k e / inner ℝ e e) • e
  have hxi : inner ℝ xi e=0 := by
    dsimp [xi]
    simp only [inner_sub_left,real_inner_smul_left,div_mul_cancel₀ _ hee,sub_self]
  have hxik := hk xi hxi
  have hxixi : inner ℝ xi xi=0 := by
    change inner ℝ xi (k-(inner ℝ k e / inner ℝ e e) • e)=0
    simp only [inner_sub_right,real_inner_smul_right,hxik,hxi,mul_zero,sub_zero]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hxixi)

lemma WeakMTW.firstcut_segment_kernel_zero (hmtw : WeakMTW (n := n) (M := M))
    {x : M} {p e k : TangentSpace 𝓘(ℝ,Model n) x} {a b : ℝ}
    (ha : a<0) (hb : 0<b) (he : e≠0)
    (hseg : ∀ s ∈ Icc a b, p+s • e ∈ minimizingVectors x)
    (hleft : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x (p+a • e)) (riemannianExp x v)) (p+a • e)))
    (hright : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x (p+b • e)) (riemannianExp x v)) (p+b • e)))
    (hk : mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) (riemannianExp x) p k=0) :
    k=0 := by
  by_contra hk0
  have hpar := kernel_parallel_of_transverse_orthogonal_ne_zero he
    (hmtw.firstcut_kernel_transverse_orthogonal ha hb hseg hleft hright hk)
  have hpair : inner ℝ k e≠0 := by
    intro hh
    rw [hh,zero_div,zero_smul] at hpar
    exact hk0 hpar
  have hortho : inner ℝ p e=0 := by
    have hh := exp_kernel_radial_orthogonal hk
    rw [hpar,real_inner_smul_right] at hh
    exact (mul_eq_zero.mp hh).resolve_left (div_ne_zero hpair (inner_self_ne_zero.mpr he))
  have hp : p ∈ minimizingVectors x := by simpa using hseg 0 ⟨ha.le,hb.le⟩
  have hnear : ∀ᶠ s : ℝ in 𝓝 0, p+s • e ∈ minimizingVectors x := by
    filter_upwards [Ioo_mem_nhds ha hb] with s hs
    exact hseg s ⟨hs.1.le,hs.2.le⟩
  obtain ⟨eps,B,c,heps,hc,hupper⟩ := conjugate_curved_hessian_upper hp hnear hk hpair
  obtain ⟨D,hD⟩ := hmtw.firstcut_radial_lower hb
    (fun s hs => hseg s ⟨ha.le.trans hs.1,hs.2⟩) hright hortho
  have hcurve : Tendsto (fun s : ℝ => 1-s^2) (𝓝[>] 0) (𝓝[<] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (show ContinuousAt (fun s : ℝ => 1-s^2) 0 from by fun_prop).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      change 1-s^2<1
      have hs0 : 0<s := hs
      nlinarith [sq_pos_of_pos hs0]
  have hpoly : ∀ᶠ s : ℝ in 𝓝[>] 0, c≤D*s+B*s^2 := by
    filter_upwards [hcurve.eventually hD,self_mem_nhdsWithin,
      (eventually_lt_nhds heps).filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with s hs hs0 hseps hsb
    have hspos : 0<s := hs0
    have hlo := hs s ⟨hspos.le,hsb.le⟩
    have hhi := hupper s ⟨hspos,hseps⟩
    have hdiv : c/s^2≤B-hessianValue x ((1-s^2) • (p+s • e)) e := by linarith
    have hmul := (div_le_iff₀ (sq_pos_of_pos hspos)).mp hdiv
    nlinarith
  have htend : Tendsto (fun s : ℝ => D*s+B*s^2) (𝓝[>] 0) (𝓝 0) := by
    simpa using (show ContinuousAt (fun s : ℝ => D*s+B*s^2) 0 from by fun_prop).tendsto.mono_left nhdsWithin_le_nhds
  have hc0 : c≤0 := le_of_tendsto_of_tendsto tendsto_const_nhds htend hpoly
  exact (not_le_of_gt hc) hc0
end WeakMTWTransport

end

end OAI
