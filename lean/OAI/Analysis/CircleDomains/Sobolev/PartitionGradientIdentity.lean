import OAI.Analysis.CircleDomains.Sobolev.PartitionErrorSum

namespace OAI

/-! The total selected error is the derivative of the smooth partition
sum minus the corresponding partition of local weak gradients. -/

open Set Function Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity
namespace OpenPlanePartition

variable {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
  (ρ : OpenPlanePartition Ω ι)

theorem finite_weights_and_derivatives {x : EuclideanPlane} (hx : x ∈ Ω) :
    ∃s : Finset ι,
      (∀j ∉ s, ρ.weight j x = 0 ∧ fderiv ℝ (ρ.weight j) x = 0) ∧
      (ρ.mix (fun _ _ => 1) =ᶠ[𝓝 x] fun y => ∑j ∈ s, ρ.weight j y) ∧
      (∑j ∈ s, ρ.weight j x) = 1 ∧ (∑j ∈ s, fderiv ℝ (ρ.weight j) x) = 0 := by
  classical
  obtain ⟨s, hs⟩ := ρ.eventually_finite_weights hx
  have heq : ρ.mix (fun _ _ => 1) =ᶠ[𝓝 x] fun y => ∑j ∈ s, ρ.weight j y := by
    filter_upwards [hs] with y hy
    simp only [mix, mul_one]
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra hjs
    exact hj (hy j hjs)
  have hone : (fun y => ∑j ∈ s, ρ.weight j y) =ᶠ[𝓝 x] (fun _ => 1) := by
    filter_upwards [hs, Ω.isOpen.mem_nhds hx] with y hy hyΩ
    rw [← ρ.sum_one ⟨y, hyΩ⟩]
    symm
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra hjs
    exact hj (hy j hjs)
  refine ⟨s, ?_, heq, hone.eq_of_nhds, ?_⟩
  · intro j hj
    have hz : ρ.weight j =ᶠ[𝓝 x] (fun _ => 0) := hs.mono fun _ hy => hy j hj
    refine ⟨hz.eq_of_nhds, ?_⟩
    rw [hz.fderiv_eq]
    exact fderiv_const_apply 0
  · calc
      _ = fderiv ℝ (fun y => ∑j ∈ s, ρ.weight j y) x :=
        (fderiv_fun_sum (fun j _ => (ρ.smooth j).differentiable (by simp) x)).symm
      _ = fderiv ℝ (fun _ : EuclideanPlane => (1 : ℝ)) x := hone.fderiv_eq
      _ = 0 := fderiv_const_apply 1

theorem mix_gradient_error_identity
    (u : EuclideanPlane → ℝ) (G : ι → EuclideanPlane → EuclideanPlane)
    (v : ι → EuclideanPlane → ℝ) (hv : ∀j, ContDiff ℝ (⊤ : ℕ∞) (v j))
    {x : EuclideanPlane} (hx : x ∈ Ω) (i : Fin 2) :
    (fderiv ℝ (ρ.mix v) x) (EuclideanSpace.single i 1) -
      (∑ᶠ j, ρ.weight j x * G j x i) =
      ∑ᶠ j, partitionDerivativeError ρ u G v i j x := by
  classical
  obtain ⟨s, hz, _, _, hd⟩ := ρ.finite_weights_and_derivatives hx
  have hmix := ρ.mix_fderiv v hv hx
  have hzero (j : ι) (hj : j ∉ s) :
      fderiv ℝ (fun y => ρ.weight j y * v j y) x = 0 := by
    rw [fderiv_fun_mul ((ρ.smooth j).differentiable (by simp) x)
      ((hv j).differentiable (by simp) x), (hz j hj).1, (hz j hj).2]
    simp
  have hf : (∑ᶠ j, fderiv ℝ (fun y => ρ.weight j y * v j y) x) =
      ∑j ∈ s, fderiv ℝ (fun y => ρ.weight j y * v j y) x := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra hjs
    exact hj (hzero j hjs)
  have hG : (∑ᶠ j, ρ.weight j x * G j x i) = ∑j ∈ s, ρ.weight j x * G j x i := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra hjs
    apply hj
    change ρ.weight j x * G j x i = 0
    rw [(hz j hjs).1, zero_mul]
  have herr : (∑ᶠ j, partitionDerivativeError ρ u G v i j x) =
      ∑j ∈ s, partitionDerivativeError ρ u G v i j x := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra hjs
    apply hj
    change partitionDerivativeError ρ u G v i j x = 0
    simp only [partitionDerivativeError, (hz j hjs).1, (hz j hjs).2,
      zero_apply, zero_mul, zero_add]
  have hd' : (∑j ∈ s, (fderiv ℝ (ρ.weight j) x) (EuclideanSpace.single i 1)) = 0 := by
    simpa only [sum_apply, zero_apply] using
      congrArg (fun A : EuclideanPlane →L[ℝ] ℝ => A (EuclideanSpace.single i 1)) hd
  rw [hmix, hf, hG, herr]
  simp only [sum_apply]
  have hprod (j : ι) :
      (fderiv ℝ (fun y => ρ.weight j y * v j y) x) (EuclideanSpace.single i 1) =
      ρ.weight j x * (fderiv ℝ (v j) x) (EuclideanSpace.single i 1) +
      (fderiv ℝ (ρ.weight j) x) (EuclideanSpace.single i 1) * v j x := by
    rw [fderiv_fun_mul ((ρ.smooth j).differentiable (by simp) x)
      ((hv j).differentiable (by simp) x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  simp_rw [hprod, partitionDerivativeError, mul_sub]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.sum_mul, hd']
  ring

end OpenPlanePartition
end CircleDomainRigidity

end

end OAI
