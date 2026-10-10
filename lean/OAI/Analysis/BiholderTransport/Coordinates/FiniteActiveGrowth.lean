import Mathlib
import OAI.Analysis.BiholderTransport.CostGeometry.StrictDividedAction
import OAI.Analysis.BiholderTransport.Calculus.FiniteSmoothTransverseGrowth
import OAI.Analysis.BiholderTransport.Regularity.SecondScaled

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

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma normalCost_hasFDerivAt_zero {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ injectivityDomain x) :
    HasFDerivAt (normalCost x p) (innerSL ℝ (-p)) 0 := by
  apply ((normalCost_contDiffAt hp).differentiableAt (by simp)).hasFDerivAt.congr_fderiv
  ext v
  have H := (normalCost_radial_fderiv_near_zero hp v).self_of_nhds
  simpa only [zero_smul,zero_sub,neg_one_mul,innerSL_apply_apply,inner_neg_left] using H

lemma WeakMTW.finite_active_cost_growth (hmtw : WeakMTW (n := n) (M := M))
    {ι : Type*} [Fintype ι] [Nonempty ι] {x : M}
    (p : ι → TangentSpace 𝓘(ℝ,Model n) x) (w : ι → ℝ)
    (hw : ∀ i, 0<w i) (hsum : ∑ i, w i=1)
    (hmin : ∀ i, p i ∈ minimizingVectors x)
    {t s : ℝ} (ht : 0<t) (hts : t<s) (hs : s<1)
    (hID : ∀ q ∈ convexHull ℝ (range p), t • q ∈ injectivityDomain x) :
    ∃ b>0, ∀ᶠ h : TangentSpace 𝓘(ℝ,Model n) x in 𝓝 0, ∃ i,
      b*‖h‖^2≤
        (normalCost x (t • (∑ j, w j • p j)) h-normalCost x (t • (∑ j, w j • p j)) 0)/t-
        (normalCost x (s • p i) h-normalCost x (s • p i) 0)/s := by
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
    inferInstanceAs (FiniteDimensional ℝ (Model n))
  let r := ∑ j, w j • p j
  have hrh : r ∈ convexHull ℝ (range p) :=
    (convex_convexHull ℝ (range p)).sum_mem (fun i _ => (hw i).le) hsum
      (fun i _ => subset_convexHull ℝ (range p) (mem_range_self i))
  have hrt := hID r hrh
  have hsi : ∀ i, s • p i ∈ injectivityDomain x :=
    fun i => contracted_minimizer_mem_injectivityDomain (hmin i) (ht.trans hts) hs
  let f := fun i (h : TangentSpace 𝓘(ℝ,Model n) x) =>
    t⁻¹*(normalCost x (t • r) h-normalCost x (t • r) 0)-
    s⁻¹*(normalCost x (s • p i) h-normalCost x (s • p i) 0)
  have hleft : ContDiffAt ℝ 2 (normalCost x (t • r)) 0 :=
    (normalCost_contDiffAt hrt).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hright : ∀ i, ContDiffAt ℝ 2 (normalCost x (s • p i)) 0 :=
    fun i => (normalCost_contDiffAt (hsi i)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hf : ∀ i, ContDiffAt ℝ 2 (f i) 0 := fun i =>
    (contDiffAt_const.mul (hleft.sub contDiffAt_const)).sub
      (contDiffAt_const.mul ((hright i).sub contDiffAt_const))
  have hfirst : ∀ i, fderiv ℝ (f i) 0=innerSL ℝ (p i-r) := by
    intro i
    have H := (((normalCost_hasFDerivAt_zero hrt).sub_const (normalCost x (t • r) 0)).const_smul t⁻¹).sub
      (((normalCost_hasFDerivAt_zero (hsi i)).sub_const (normalCost x (s • p i) 0)).const_smul s⁻¹)
    have H' : HasFDerivAt (f i) (innerSL ℝ (p i-r)) 0 := by
      apply H.congr_fderiv
      ext v
      simp only [sub_apply,smul_apply,innerSL_apply_apply,inner_neg_left,
        real_inner_smul_left,inner_sub_left,smul_eq_mul]
      field_simp [ht.ne', (ht.trans hts).ne']
      ring
    exact H'.fderiv
  have hsecond : ∀ i v, fderiv ℝ (fderiv ℝ (f i)) 0 v v=
      hessianValue x (t • r) v/t-hessianValue x (s • p i) v/s := by
    intro i v
    rw [second_fderiv_scaled_differences hleft (hright i)]
    rw [hessianValue_eq_normalHessian hrt,hessianValue_eq_normalHessian (hsi i)]
    simp only [normalHessian,div_eq_mul_inv]
    ring
  have hmean : ∀ v, ∑ i, w i*fderiv ℝ (f i) 0 v=0 := by
    intro v
    simp only [hfirst,innerSL_apply_apply,inner_sub_left,mul_sub,Finset.sum_sub_distrib,
      ←Finset.sum_mul,hsum,one_mul]
    have heq : (∑ i, w i*inner ℝ (p i) v)=inner ℝ r v := by
      simp only [r,sum_inner,real_inner_smul_left]
    rw [heq,sub_self]
  have hpos : ∀ v, v≠0 → (∀ i, fderiv ℝ (f i) 0 v=0) →
      0<∑ i, w i*fderiv ℝ (fderiv ℝ (f i)) 0 v v := by
    intro v hv hl
    have hortho : ∀ i, inner ℝ v (p i-r)=0 := by
      intro i
      rw [real_inner_comm]
      simpa only [hfirst,innerSL_apply_apply] using hl i
    have H := hmtw.finite_transverse_slack_strict p w hw hsum hmin ht hts hs hID hv hortho
    simp only [hsecond,mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,hsum,one_mul]
    exact sub_pos.mpr H
  obtain ⟨b,hb,H⟩ := finite_smooth_transverse_growth f hf (fun i => by simp [f]) w hw hsum hmean hpos
  refine ⟨b,hb,?_⟩
  filter_upwards [H] with h hh
  obtain ⟨i,hi⟩ := hh
  refine ⟨i,?_⟩
  simpa only [f,r,div_eq_mul_inv,mul_comm] using hi
end WeakMTWTransport

end

end OAI
