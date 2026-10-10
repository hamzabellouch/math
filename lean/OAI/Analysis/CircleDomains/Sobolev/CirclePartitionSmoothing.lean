import OAI.Analysis.CircleDomains.Sobolev.PartitionMixing
import OAI.Analysis.CircleDomains.Topology.CircleLiftTransitions

namespace OAI

/-! Gluing smooth approximants to continuous real circle branches. The
integer transition functions cancel in the partition sum. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

namespace OpenPlanePartition
variable {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} (ρ : OpenPlanePartition Ω ι)

 theorem mix_add_scalar (v : ι → EuclideanPlane → ℝ) (c : EuclideanPlane → ℝ)
    {x : EuclideanPlane} (hx : x ∈ Ω) :
    ρ.mix (fun i y => v i y + c y) x = ρ.mix v x + c x := by
  classical
  let s := (ρ.point_finite x).toFinset
  have hz (i : ι) (hi : i ∉ s) : ρ.weight i x = 0 := by
    by_contra h
    exact hi ((ρ.point_finite x).mem_toFinset.mpr h)
  have hs (f : ι → ℝ) : (∑ᶠ i, ρ.weight i x * f i) = ∑ i ∈ s, ρ.weight i x * f i := by
    apply finsum_eq_sum_of_support_subset
    intro i hi
    by_contra his
    apply hi
    change ρ.weight i x * f i = 0
    rw [hz i his, zero_mul]
  have hone : (∑ i ∈ s, ρ.weight i x) = 1 := by
    have hh := hs (fun _ => 1)
    simp only [mul_one] at hh
    exact hh.symm.trans (ρ.sum_one ⟨x, hx⟩)
  change (∑ᶠ i, ρ.weight i x * (v i x + c x)) = (∑ᶠ i, ρ.weight i x * v i x) + c x
  rw [hs (fun i => v i x + c x), hs (fun i => v i x)]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hone, one_mul]

 def circleMix (f : EuclideanPlane → UnitAddCircle) (u v : ι → EuclideanPlane → ℝ)
    (x : EuclideanPlane) : UnitAddCircle :=
  f x + (ρ.mix (fun i y => v i y - u i y) x : UnitAddCircle)

 theorem circleMix_smooth
    (W : ι → Set EuclideanPlane) (hW : ∀ i, IsOpen (W i))
    (hsub : ∀ i, tsupport (ρ.weight i) ⊆ W i)
    (f : EuclideanPlane → UnitAddCircle) (u v : ι → EuclideanPlane → ℝ)
    (hu : ∀ i, ContinuousOn (u i) (W i))
    (hlift : ∀ i x, x ∈ W i → (u i x : UnitAddCircle) = f x)
    (hv : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (v i)) :
    SmoothCircleOn (ρ.circleMix f u v) Ω := by
  classical
  intro x hx a ha
  have hj : ∃ j, ρ.weight j x ≠ 0 := by
    by_contra hn
    have hz : ∀ j, ρ.weight j x = 0 := fun j => not_not.mp (fun h => hn ⟨j, h⟩)
    have hh := ρ.sum_one ⟨x, hx⟩
    simp only [hz, finsum_zero] at hh
    norm_num at hh
  obtain ⟨j, hj⟩ := hj
  have hxj : x ∈ W j := hsub j (subset_tsupport (ρ.weight j) hj)
  let r : ι → EuclideanPlane → ℝ := fun i y => v i y + (u j y - u i y)
  have hterm (i : ι) : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => ρ.weight i y * r i y) x := by
    by_cases hi : x ∈ tsupport (ρ.weight i)
    · have hxi := hsub i hi
      have ht := circle_lift_difference_contDiffAt ((hW j).inter (hW i))
        ((hu j).mono inter_subset_left) ((hu i).mono inter_subset_right)
        (fun y hy => (hlift j y hy.1).trans (hlift i y hy.2).symm) ⟨hxj, hxi⟩
      exact (ρ.smooth i).contDiffAt.mul ((hv i).contDiffAt.add ht)
    · have hz : (fun y => ρ.weight i y * r i y) =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [(isClosed_tsupport (ρ.weight i)).isOpen_compl.mem_nhds hi] with y hy
        rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hz
  obtain ⟨s, hs⟩ := ρ.mix_eventually_eq_sum r hx
  have hr : ContDiffAt ℝ (⊤ : ℕ∞) (ρ.mix r) x :=
    (ContDiffAt.sum (fun i _ => hterm i)).congr_of_eventuallyEq hs
  have he : ρ.circleMix f u v =ᶠ[𝓝 x] (fun y => (ρ.mix r y : UnitAddCircle)) := by
    filter_upwards [Ω.isOpen.mem_nhds hx, (hW j).mem_nhds hxj] with y hyΩ hyj
    rw [circleMix, ← hlift j y hyj, ← AddCircle.coe_add]
    congr 1
    have hm := ρ.mix_add_scalar (fun i y => v i y - u i y) (u j) hyΩ
    have hre : r = fun i y => (v i y - u i y) + u j y := by
      funext i y
      dsimp [r]
      ring
    rw [hre, hm, add_comm]
  have hne : (ρ.mix r x : UnitAddCircle) ≠ (a : UnitAddCircle) := he.eq_of_nhds ▸ ha
  have hchart := contDiffAt_circle_quotient_chart hr a hne
  exact hchart.congr_of_eventuallyEq (he.mono fun y hy => congrArg
    (fun z => (AddCircle.equivIco (1 : ℝ) a z : ℝ)) hy)

 theorem mix_sub_continuousOn
    (W : ι → Set EuclideanPlane) (hW : ∀ i, IsOpen (W i))
    (hsub : ∀ i, tsupport (ρ.weight i) ⊆ W i)
    (u v : ι → EuclideanPlane → ℝ)
    (hu : ∀ i, ContinuousOn (u i) (W i)) (hv : ∀ i, Continuous (v i)) :
    ContinuousOn (ρ.mix (fun i y => v i y - u i y)) Ω := by
  intro x hx
  have hterm (i : ι) : ContinuousAt (fun y => ρ.weight i y * (v i y - u i y)) x := by
    by_cases hi : x ∈ tsupport (ρ.weight i)
    · exact (ρ.smooth i).continuous.continuousAt.mul
        ((hv i).continuousAt.sub ((hu i).continuousAt ((hW i).mem_nhds (hsub i hi))))
    · have hz : (fun y => ρ.weight i y * (v i y - u i y)) =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [(isClosed_tsupport (ρ.weight i)).isOpen_compl.mem_nhds hi] with y hy
        rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
      exact continuousAt_const.congr_of_eventuallyEq hz
  obtain ⟨s, hs⟩ := ρ.mix_eventually_eq_sum (fun i y => v i y - u i y) hx
  have hsum : ContinuousAt (fun y => ∑ i ∈ s, ρ.weight i y * (v i y - u i y)) x := by
    classical
    clear hs
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using
        (continuousAt_const : ContinuousAt (fun _ : EuclideanPlane => (0 : ℝ)) x)
    | @insert i s hi ih =>
        have hh : ContinuousAt (fun y => ρ.weight i y * (v i y - u i y) +
            ∑ k ∈ s, ρ.weight k y * (v k y - u k y)) x := (hterm i).add ih
        simpa only [Finset.sum_insert hi] using hh
  exact (hsum.congr_of_eventuallyEq hs).continuousWithinAt

end OpenPlanePartition
end CircleDomainRigidity

end

end OAI
