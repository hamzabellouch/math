import Mathlib

namespace OAI

/-! Kernel Compact. -/

section

 

noncomputable section
open Set Filter Topology
open scoped BoundedContinuousFunction
namespace EllipticCompact
variable {K H : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

def kernelOperator (g : K →ᵇ (H →L[ℂ] ℂ)) : H →L[ℂ] (K →ᵇ ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun u => BoundedContinuousFunction.mkOfCompact
        ⟨fun x => g x u, by fun_prop⟩
      map_add' := by intro u v; ext x; exact map_add (g x) u v
      map_smul' := by intro c u; ext x; exact map_smul (g x) c u }
    ‖g‖ (fun u => by
      change ‖BoundedContinuousFunction.mkOfCompact ⟨fun x => g x u, _⟩‖ ≤ ‖g‖ * ‖u‖
      apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg g) (norm_nonneg u))).mpr
      intro x
      exact ((g x).le_opNorm u).trans (mul_le_mul_of_nonneg_right (g.norm_coe_le_norm x) (norm_nonneg _)))

lemma kernelOperator_apply (g : K →ᵇ (H →L[ℂ] ℂ)) (u : H) (x : K) :
    kernelOperator g u x = g x u := rfl

 

theorem kernelOperator_compact (g : K →ᵇ (H →L[ℂ] ℂ)) :
    IsCompactOperator (kernelOperator g) := by
  let S := kernelOperator g '' Metric.closedBall (0 : H) 1
  have heq : Equicontinuous ((↑) : S → K → ℂ) := by
    intro x
    apply Metric.equicontinuousAt_of_continuity_modulus
      (b := fun y => ‖g x - g y‖)
    · have h : ContinuousAt (fun y => ‖g x - g y‖) x := by fun_prop
      simpa using h.tendsto
    · filter_upwards [] with y F
      obtain ⟨u, hu, hF⟩ := F.property
      have hn : ‖u‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hu
      change dist (F.val x) (F.val y) ≤ _
      rw [← hF, kernelOperator_apply, kernelOperator_apply, dist_eq_norm,
        ← sub_apply]
      exact ((g x - g y).le_opNorm u).trans (by simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left hn (norm_nonneg (g x - g y))))
  have hc : IsCompact (closure S) := BoundedContinuousFunction.arzela_ascoli
    (Metric.closedBall (0 : ℂ) ‖g‖) (isCompact_closedBall _ _) S (by
      intro F x hF
      obtain ⟨u, hu, rfl⟩ := hF
      have hn : ‖u‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hu
      rw [Metric.mem_closedBall, dist_zero_right, kernelOperator_apply]
      exact ((g x).le_opNorm u).trans ((mul_le_mul_of_nonneg_right (g.norm_coe_le_norm x) (norm_nonneg _)).trans
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hn (norm_nonneg g)))) heq
  apply (isCompactOperator_iff_exists_mem_nhds_image_subset_compact _).mpr
  exact ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds _ (by norm_num), closure S, hc,
    subset_closure⟩
end EllipticCompact

end
end

end OAI
