import OAI.Analysis.CircleDomains.Topology.CirclePartitionBands
import OAI.Analysis.CircleDomains.Sobolev.PartitionLocalDerivatives
import OAI.Analysis.CircleDomains.Sobolev.CircleDifferential

namespace OAI

/-! The derivative of every local branch of the smoothed circle map.
The integer transition derivatives vanish and the partition derivatives
sum to zero, leaving one global scalar derivative expression. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
namespace OpenPlanePartition

variable {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} (ρ : OpenPlanePartition Ω ι)

 theorem adjustedCircleMix_contDiffAt
    (W : ι → Set EuclideanPlane) (hW : ∀ k, IsOpen (W k))
    (hsub : ∀ k, tsupport (ρ.weight k) ⊆ W k)
    (f : EuclideanPlane → UnitAddCircle) (u v : ι → EuclideanPlane → ℝ)
    (hu : ∀ k, ContinuousOn (u k) (W k))
    (hlift : ∀ k y, y ∈ W k → (u k y : UnitAddCircle) = f y)
    (hv : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (v k))
    (j : ι) {x : EuclideanPlane} (hx : x ∈ Ω) (hxj : x ∈ W j) :
    ContDiffAt ℝ (⊤ : ℕ∞) (ρ.adjustedCircleMix u v (u j)) x := by
  classical
  let r : ι → EuclideanPlane → ℝ := fun k y => v k y + (u j y - u k y)
  have hterm (k : ι) : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => ρ.weight k y * r k y) x := by
    by_cases hk : x ∈ tsupport (ρ.weight k)
    · have ht := circle_lift_difference_contDiffAt ((hW j).inter (hW k))
        ((hu j).mono inter_subset_left) ((hu k).mono inter_subset_right)
        (fun y hy => (hlift j y hy.1).trans (hlift k y hy.2).symm) ⟨hxj, hsub k hk⟩
      exact (ρ.smooth k).contDiffAt.mul ((hv k).contDiffAt.add ht)
    · have hz : (fun y => ρ.weight k y * r k y) =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [(isClosed_tsupport (ρ.weight k)).isOpen_compl.mem_nhds hk] with y hy
        rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hz
  obtain ⟨s, hs⟩ := ρ.mix_eventually_eq_sum r hx
  exact (ContDiffAt.sum (fun k _ => hterm k)).congr_of_eventuallyEq hs

 theorem adjustedCircleMix_derivative
    (W : ι → Set EuclideanPlane) (hW : ∀ k, IsOpen (W k))
    (hsub : ∀ k, tsupport (ρ.weight k) ⊆ W k)
    (f : EuclideanPlane → UnitAddCircle) (u v : ι → EuclideanPlane → ℝ)
    (hu : ∀ k, ContinuousOn (u k) (W k))
    (hlift : ∀ k y, y ∈ W k → (u k y : UnitAddCircle) = f y)
    (hv : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (v k))
    (j : ι) {x : EuclideanPlane} (hx : x ∈ Ω) (hxj : x ∈ W j) (i : Fin 2) :
    (fderiv ℝ (ρ.adjustedCircleMix u v (u j)) x) (EuclideanSpace.single i 1) =
      ∑ᶠ k, (ρ.weight k x * (fderiv ℝ (v k) x) (EuclideanSpace.single i 1) +
        (fderiv ℝ (ρ.weight k) x) (EuclideanSpace.single i 1) * (v k x - u k x)) := by
  classical
  let r : ι → EuclideanPlane → ℝ := fun k y => v k y + (u j y - u k y)
  have hp (k : ι) :
      DifferentiableAt ℝ (fun y => ρ.weight k y * r k y) x ∧
      (fderiv ℝ (fun y => ρ.weight k y * r k y) x) (EuclideanSpace.single i 1) =
        ρ.weight k x * (fderiv ℝ (v k) x) (EuclideanSpace.single i 1) +
          (fderiv ℝ (ρ.weight k) x) (EuclideanSpace.single i 1) * r k x := by
    by_cases hk : x ∈ tsupport (ρ.weight k)
    · have hxk := hsub k hk
      have ht := circle_lift_difference_eventually_constant ((hW j).inter (hW k))
        ((hu j).mono inter_subset_left) ((hu k).mono inter_subset_right)
        (fun y hy => (hlift j y hy.1).trans (hlift k y hy.2).symm) ⟨hxj, hxk⟩
      have hdiff : DifferentiableAt ℝ (fun y => u j y - u k y) x :=
        ((show ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : EuclideanPlane => u j x - u k x) x from
          contDiffAt_const).congr_of_eventuallyEq ht).differentiableAt (by simp)
      have hd : fderiv ℝ (fun y => u j y - u k y) x = 0 := by
        rw [ht.fderiv_eq]
        exact fderiv_const_apply _
      have hrv : DifferentiableAt ℝ (r k) x := ((hv k).differentiable (by simp) x).add hdiff
      refine ⟨((ρ.smooth k).differentiable (by simp) x).mul hrv, ?_⟩
      rw [fderiv_fun_mul ((ρ.smooth k).differentiable (by simp) x) hrv]
      change ((ρ.weight k x) • fderiv ℝ (fun y => v k y + (u j y - u k y)) x +
        r k x • fderiv ℝ (ρ.weight k) x) (EuclideanSpace.single i 1) = _
      rw [fderiv_fun_add ((hv k).differentiable (by simp) x) hdiff, hd, add_zero]
      simp only [add_apply, smul_apply, smul_eq_mul, mul_comm (r k x)]
    · have hz : (fun y => ρ.weight k y * r k y) =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [(isClosed_tsupport (ρ.weight k)).isOpen_compl.mem_nhds hk] with y hy
        rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
      refine ⟨((show ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : EuclideanPlane => (0 : ℝ)) x from
        contDiffAt_const).congr_of_eventuallyEq hz).differentiableAt (by simp), ?_⟩
      rw [hz.fderiv_eq, fderiv_const_apply, image_eq_zero_of_notMem_tsupport hk,
        fderiv_of_notMem_tsupport ℝ hk]
      simp
  obtain ⟨s, hs, _, _, hd⟩ := ρ.finite_weights_and_derivatives hx
  have hleft : (∑ᶠ k, fderiv ℝ (fun y => ρ.weight k y * r k y) x) =
      ∑ k ∈ s, fderiv ℝ (fun y => ρ.weight k y * r k y) x := by
    apply finsum_eq_sum_of_support_subset
    intro k hk
    by_contra hks
    apply hk
    change fderiv ℝ (fun y => ρ.weight k y * r k y) x = 0
    have hw : ρ.weight k x = 0 := (hs k hks).1
    have hdw : fderiv ℝ (ρ.weight k) x = 0 := (hs k hks).2
    by_cases ht : x ∈ tsupport (ρ.weight k)
    · have hxk := hsub k ht
      have hdiff := circle_lift_difference_contDiffAt ((hW j).inter (hW k))
        ((hu j).mono inter_subset_left) ((hu k).mono inter_subset_right)
        (fun y hy => (hlift j y hy.1).trans (hlift k y hy.2).symm) ⟨hxj, hxk⟩
      have hr := (hv k).contDiffAt.add hdiff
      rw [fderiv_fun_mul ((ρ.smooth k).differentiable (by simp) x)
        (hr.differentiableAt (by simp)), hw, hdw]
      simp
    · have hzero : (fun y => ρ.weight k y * r k y) =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [(isClosed_tsupport (ρ.weight k)).isOpen_compl.mem_nhds ht] with y hy
        rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
      rw [hzero.fderiv_eq]
      exact fderiv_const_apply 0
  have hright : (∑ᶠ k, (ρ.weight k x * (fderiv ℝ (v k) x) (EuclideanSpace.single i 1) +
      (fderiv ℝ (ρ.weight k) x) (EuclideanSpace.single i 1) * (v k x - u k x))) =
      ∑ k ∈ s, (ρ.weight k x * (fderiv ℝ (v k) x) (EuclideanSpace.single i 1) +
        (fderiv ℝ (ρ.weight k) x) (EuclideanSpace.single i 1) * (v k x - u k x)) := by
    apply finsum_eq_sum_of_support_subset
    intro k hk
    by_contra hks
    apply hk
    simp only [(hs k hks).1, (hs k hks).2, zero_apply, zero_mul, zero_add]
  have hd' : (∑ k ∈ s, (fderiv ℝ (ρ.weight k) x) (EuclideanSpace.single i 1)) = 0 := by
    simpa only [sum_apply, zero_apply] using
      congrArg (fun A : EuclideanPlane →L[ℝ] ℝ => A (EuclideanSpace.single i 1)) hd
  change (fderiv ℝ (ρ.mix r) x) _ = _
  rw [ρ.mix_fderiv_of_products r hx (fun k => (hp k).1), hleft, hright]
  simp only [sum_apply]
  have heq (k : ι) :
      (fderiv ℝ (fun y => ρ.weight k y * r k y) x) (EuclideanSpace.single i 1) =
        (ρ.weight k x * (fderiv ℝ (v k) x) (EuclideanSpace.single i 1) +
          (fderiv ℝ (ρ.weight k) x) (EuclideanSpace.single i 1) * (v k x - u k x)) +
        (fderiv ℝ (ρ.weight k) x) (EuclideanSpace.single i 1) * u j x := by
    rw [(hp k).2]
    dsimp [r]
    ring
  simp_rw [heq]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hd', zero_mul, add_zero]

 theorem circleMix_derivative
    (W : ι → Set EuclideanPlane) (hW : ∀ k, IsOpen (W k))
    (hsub : ∀ k, tsupport (ρ.weight k) ⊆ W k)
    (f : EuclideanPlane → UnitAddCircle) (u v : ι → EuclideanPlane → ℝ)
    (hu : ∀ k, ContinuousOn (u k) (W k))
    (hlift : ∀ k y, y ∈ W k → (u k y : UnitAddCircle) = f y)
    (hv : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (v k))
    {x : EuclideanPlane} (hx : x ∈ Ω) (i : Fin 2) :
    FiniteTransfer.circleFDeriv (ρ.circleMix f u v) x (EuclideanSpace.single i 1) =
      ∑ᶠ k, (ρ.weight k x * (fderiv ℝ (v k) x) (EuclideanSpace.single i 1) +
        (fderiv ℝ (ρ.weight k) x) (EuclideanSpace.single i 1) * (v k x - u k x)) := by
  classical
  have hj : ∃ j, ρ.weight j x ≠ 0 := by
    by_contra hn
    have hz : ∀ j, ρ.weight j x = 0 := fun j => not_not.mp (fun h => hn ⟨j, h⟩)
    have hh := ρ.sum_one ⟨x, hx⟩
    simp only [hz, finsum_zero] at hh
    norm_num at hh
  obtain ⟨j, hj⟩ := hj
  have hxj := hsub j (subset_tsupport (ρ.weight j) hj)
  have hsm := ρ.circleMix_smooth W hW hsub f u v hu hlift hv
  have hr := ρ.adjustedCircleMix_contDiffAt W hW hsub f u v hu hlift hv j hx hxj
  have he : (fun y => (ρ.adjustedCircleMix u v (u j) y : UnitAddCircle))
      =ᶠ[𝓝 x] ρ.circleMix f u v := by
    filter_upwards [Ω.isOpen.mem_nhds hx, (hW j).mem_nhds hxj] with y hy hyj
    exact (ρ.circleMix_eq_adjusted f u v (u j) hy (hlift j y hyj)).symm
  rw [FiniteTransfer.circleFDeriv_eq_lift
    (hsm.continuousOn.continuousAt (Ω.isOpen.mem_nhds hx)) hr.continuousAt he]
  exact ρ.adjustedCircleMix_derivative W hW hsub f u v hu hlift hv j hx hxj i

end OpenPlanePartition
end CircleDomainRigidity

end

end OAI
