import OAI.Analysis.CircleDomains.Sobolev.LocalSmoothPartition
import Mathlib.Analysis.Convex.Combination

namespace OAI

/-! Smooth mixing on an open planar domain. The locally finite sum is
represented by an actual finite sum in a neighborhood of each point. -/

open Set Function Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity
namespace OpenPlanePartition

variable {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
  (ρ : OpenPlanePartition Ω ι)

def mix (v : ι → EuclideanPlane → ℝ) (x : EuclideanPlane) : ℝ :=
  ∑ᶠ i, ρ.weight i x * v i x

theorem point_finite (x : EuclideanPlane) : HasFiniteSupport (fun i => ρ.weight i x) := by
  by_cases hx : x ∈ Ω
  · exact ρ.locallyFinite.point_finite ⟨x, hx⟩
  · have hz : ∀i, ρ.weight i x = 0 := fun i =>
      image_eq_zero_of_notMem_tsupport (fun h => hx (ρ.inside i h))
    change (Function.support (fun i => ρ.weight i x)).Finite
    apply finite_empty.subset
    intro i hi
    exact False.elim (hi (hz i))

theorem mix_mem_Icc (v : ι → EuclideanPlane → ℝ) {x : EuclideanPlane}
    (hx : x ∈ Ω) {a b : ℝ} (hv : ∀i, ρ.weight i x ≠ 0 → v i x ∈ Icc a b) :
    ρ.mix v x ∈ Icc a b := by
  simpa only [mix, smul_eq_mul] using (convex_Icc a b).finsum_mem
    (fun i => ρ.nonneg i x) (ρ.sum_one ⟨x, hx⟩) hv

theorem eventually_finite_weights {x : EuclideanPlane} (hx : x ∈ Ω) :
    ∃s : Finset ι, ∀ᶠ y in 𝓝 x, ∀i ∉ s, ρ.weight i y = 0 := by
  classical
  obtain ⟨T, hT, hfin⟩ := ρ.locallyFinite ⟨x, hx⟩
  refine ⟨hfin.toFinset, ?_⟩
  have hsub : ∀ᶠ y : Ω in 𝓝 ⟨x, hx⟩, ∀i ∉ hfin.toFinset, ρ.weight i y = 0 := by
    filter_upwards [hT] with y hy i hi
    by_contra hn
    apply hi
    exact hfin.mem_toFinset.mpr ⟨y, hn, hy⟩
  have hmap : ∀ᶠ y in Filter.map (Subtype.val : Ω → EuclideanPlane) (𝓝 ⟨x, hx⟩),
      ∀i ∉ hfin.toFinset, ρ.weight i y = 0 := hsub
  have hm : Filter.map (Subtype.val : Ω → EuclideanPlane) (𝓝 (⟨x, hx⟩ : Ω)) = 𝓝 x :=
    Ω.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq ⟨x, hx⟩
  rwa [hm] at hmap

theorem mix_eventually_eq_sum (v : ι → EuclideanPlane → ℝ)
    {x : EuclideanPlane} (hx : x ∈ Ω) :
    ∃s : Finset ι, ρ.mix v =ᶠ[𝓝 x] fun y => ∑ i ∈ s, ρ.weight i y * v i y := by
  classical
  obtain ⟨s, hs⟩ := ρ.eventually_finite_weights hx
  refine ⟨s, hs.mono fun y hy => ?_⟩
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra his
  apply hi
  change ρ.weight i y * v i y = 0
  rw [hy i his, zero_mul]

theorem mix_contDiffOn (v : ι → EuclideanPlane → ℝ)
    (hv : ∀i, ContDiff ℝ (⊤ : ℕ∞) (v i)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (ρ.mix v) Ω := by
  intro x hx
  obtain ⟨s, hs⟩ := ρ.mix_eventually_eq_sum v hx
  apply ContDiffAt.contDiffWithinAt
  apply ((ContDiff.sum (fun i _ => (ρ.smooth i).mul (hv i))).contDiffAt).congr_of_eventuallyEq
  exact hs

theorem mix_fderiv (v : ι → EuclideanPlane → ℝ)
    (hv : ∀i, ContDiff ℝ (⊤ : ℕ∞) (v i)) {x : EuclideanPlane} (hx : x ∈ Ω) :
    fderiv ℝ (ρ.mix v) x =
      ∑ᶠ i, fderiv ℝ (fun y => ρ.weight i y * v i y) x := by
  classical
  obtain ⟨s, hs⟩ := ρ.eventually_finite_weights hx
  have hsum : ρ.mix v =ᶠ[𝓝 x] fun y => ∑ i ∈ s, ρ.weight i y * v i y := by
    filter_upwards [hs] with y hy
    apply finsum_eq_sum_of_support_subset
    intro i hi
    by_contra his
    apply hi
    change ρ.weight i y * v i y = 0
    rw [hy i his, zero_mul]
  rw [hsum.fderiv_eq]
  rw [fderiv_fun_sum (fun i _ =>
    ((ρ.smooth i).mul (hv i)).differentiable (by simp) x)]
  symm
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra his
  apply hi
  change fderiv ℝ (fun y => ρ.weight i y * v i y) x = 0
  have hz : (fun y => ρ.weight i y * v i y) =ᶠ[𝓝 x] (fun _ => 0) :=
    hs.mono fun y hy => by
      change ρ.weight i y * v i y = 0
      rw [hy i his, zero_mul]
  rw [hz.fderiv_eq]
  exact fderiv_const_apply 0

end OpenPlanePartition

theorem finite_partition_gradient_error
    {ι : Type*} (s : Finset ι) (w dw v dv : ι → ℝ) (u G : ℝ)
    (hw : ∑i ∈ s, w i = 1) (hdw : ∑i ∈ s, dw i = 0) :
    (∑i ∈ s, (w i * dv i + dw i * v i)) - G =
      ∑i ∈ s, (w i * (dv i - G) + dw i * (v i - u)) := by
  simp_rw [mul_sub]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hw, hdw]
  ring

end CircleDomainRigidity

end

end OAI
