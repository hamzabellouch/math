import OAI.Analysis.CircleDomains.Reflection.AnalyticJordanParametrization
import OAI.Analysis.CircleDomains.Topology.SymmetricCircleAnnulus

namespace OAI

/-! The actual analytic cap can be parametrized by the unit disk, so a
fixed symmetric annulus supplies its source boundary collar. -/
open Set Function Filter Metric Complex
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exists_unit_analytic_jordan_parametrization {H:ℂ≃ₜℂ} (hH:IsAnalyticJordanCap H) :
    ∃S:Set ℂ, ∃β:ℂ→ℂ, IsOpen S ∧ closedBall 0 1⊆S ∧
      DifferentiableOn ℂ β S ∧ InjOn β S ∧
      β '' closedBall 0 1=closure (jordanInterior H) ∧
      β '' sphere 0 1=frontier (jordanInterior H) := by
  obtain ⟨W,α,c,r,hW,hr,hDW,hα,hi,hclosed,hboundary⟩ := exists_analytic_jordan_parametrization hH
  have hrc : (r:ℂ)≠0 := by exact_mod_cast hr.ne'
  let A : ℂ≃ₜℂ := (Homeomorph.mulLeft₀ (r:ℂ) hrc).trans (Homeomorph.addRight c)
  have hAnorm (z:ℂ) : ‖A z-c‖=r*‖z‖ := by
    change ‖(r:ℂ)*z+c-c‖=r*‖z‖
    rw [add_sub_cancel_right,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
  have hAc : A '' closedBall 0 1=closedBall c r := by
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      rw [mem_closedBall_iff_norm,hAnorm]
      have hz' := mem_closedBall_zero_iff.mp hz
      nlinarith
    · intro z hz
      obtain ⟨w,rfl⟩ := A.surjective z
      refine ⟨w,mem_closedBall_zero_iff.mpr ?_,rfl⟩
      rw [mem_closedBall_iff_norm,hAnorm] at hz
      nlinarith
  have hAs : A '' sphere 0 1=sphere c r := by
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      rw [mem_sphere_iff_norm,hAnorm,mem_sphere_zero_iff_norm.mp hz,mul_one]
    · intro z hz
      obtain ⟨w,rfl⟩ := A.surjective z
      refine ⟨w,mem_sphere_zero_iff_norm.mpr ?_,rfl⟩
      rw [mem_sphere_iff_norm,hAnorm] at hz
      nlinarith
  let S := A ⁻¹' W
  have hS : IsOpen S := hW.preimage A.continuous
  have hDS : closedBall (0:ℂ) 1⊆S := by
    intro z hz
    exact hDW (hAc ▸ mem_image_of_mem A hz)
  have hAd : DifferentiableOn ℂ A S := by
    intro z _
    exact (((differentiableAt_const (r:ℂ)).mul differentiableAt_id).add_const c).differentiableWithinAt
  refine ⟨S,α ∘ A,hS,hDS,hα.comp hAd (fun _ hz => hz),hi.comp A.injective.injOn (fun _ hz => hz),?_,?_⟩
  · rw [image_comp,hAc,hclosed]
  · rw [image_comp,hAs,hboundary]

lemma exists_analytic_jordan_annulus {H:ℂ≃ₜℂ} (hH:IsAnalyticJordanCap H) :
    ∃R:ℝ, ∃β:ℂ→ℂ, 1<R ∧
      DifferentiableOn ℂ β (symmetricCircleAnnulus R) ∧
      InjOn β (symmetricCircleAnnulus R) ∧
      β '' sphere 0 1=frontier (jordanInterior H) := by
  obtain ⟨S,β,hS,hDS,hβ,hi,_,hb⟩ := exists_unit_analytic_jordan_parametrization hH
  obtain ⟨R,hR,hRS⟩ := exists_symmetricCircleAnnulus_subset hS (sphere_subset_closedBall.trans hDS)
  exact ⟨R,β,hR,hβ.mono hRS,hi.mono hRS,hb⟩

end CircleDomainRigidity

end

end OAI
