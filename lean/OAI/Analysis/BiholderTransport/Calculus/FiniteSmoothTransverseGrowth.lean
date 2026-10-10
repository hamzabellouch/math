import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.FinitePositiveWeight
import OAI.Analysis.BiholderTransport.Regularity.ContDiffSecondOrder

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

namespace WeakMTWTransport
lemma finite_smooth_transverse_growth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → E → ℝ) (hf : ∀ i, ContDiffAt ℝ 2 (f i) 0) (hf0 : ∀ i, f i 0=0)
    (w : ι → ℝ) (hw : ∀ i, 0<w i) (hsum : ∑ i, w i=1)
    (hmean : ∀ v, ∑ i, w i*fderiv ℝ (f i) 0 v=0)
    (hpos : ∀ v : E, v≠0 → (∀ i, fderiv ℝ (f i) 0 v=0) →
      0<∑ i, w i*fderiv ℝ (fderiv ℝ (f i)) 0 v v) :
    ∃ b>0, ∀ᶠ h : E in 𝓝 0, ∃ i, b*‖h‖^2≤f i h := by
  let L := fun i => fderiv ℝ (f i) 0
  let B := fun i => (1/2:ℝ) • fderiv ℝ (fderiv ℝ (f i)) 0
  have hBpos : ∀ v : E, v≠0 → (∀ i, L i v=0) → 0<∑ i, w i*B i v v := by
    intro v hv hl
    have heq : (∑ i, w i*B i v v)=(1/2:ℝ)*(∑ i, w i*fderiv ℝ (fderiv ℝ (f i)) 0 v v) := by
      simp only [B,smul_apply,smul_eq_mul,Finset.mul_sum]
      congr 1
      ext i
      ring
    rw [heq]
    exact mul_pos (by norm_num) (hpos v hv hl)
  obtain ⟨b,hb,hgrowth⟩ := finite_transverse_quadratic_growth L B w hw hsum hmean hBpos
  have hrem : ∀ᶠ h : E in 𝓝 0, ∀ i,
      |f i h-L i h-B i h h|≤(b/2)*‖h‖^2 := by
    rw [Filter.eventually_all]
    intro i
    have H := (contDiffAt_second_order_remainder (hf i)).bound (half_pos hb)
    simpa only [hf0,L,B,smul_apply,smul_eq_mul,div_eq_mul_inv,one_mul,mul_comm,
      sub_zero,Real.norm_eq_abs,norm_pow,Real.norm_of_nonneg (norm_nonneg _)] using H
  refine ⟨b/2,half_pos hb,?_⟩
  filter_upwards [hgrowth,hrem] with h hh hr
  obtain ⟨i,hi⟩ := hh
  exact ⟨i,by linarith [(abs_le.mp (hr i)).1]⟩
end WeakMTWTransport

end

end OAI
