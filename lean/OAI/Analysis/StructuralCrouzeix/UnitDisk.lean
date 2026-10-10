import OAI.Analysis.StructuralCrouzeix.Model

namespace OAI

/-! Intrinsic domains, optimal similarities and matrix-valued boundary representations. -/

noncomputable section
open Set Filter Metric Complex
open scoped Topology
namespace StructuralCrouzeix

theorem isAdmissible_unitDisk : IsAdmissible (ball (0 : ℂ) 1) := by
  have hfront : frontier (ball (0 : ℂ) 1) = sphere (0 : ℂ) 1 :=
    frontier_ball _ one_ne_zero
  refine ⟨isOpen_ball, isBounded_ball, convex_ball _ _,
    ⟨0, mem_ball_self zero_lt_one⟩, ?_, ?_⟩
  · change Nonempty (↥(sphere (0 : ℂ) 1) ≃ₜ ↥(frontier (ball (0 : ℂ) 1)))
    exact ⟨Homeomorph.setCongr hfront.symm⟩
  · intro p hp
    have hpn : ‖p‖ = 1 := mem_sphere_zero_iff_norm.mp (hfront ▸ hp)
    have hp0 : p ≠ 0 := by
      intro he
      simp [he] at hpn
    let χ : ℂ → ℂ := fun z => p * exp (I * z)
    have hχa : AnalyticAt ℂ χ 0 :=
      analyticAt_const.mul ((analyticAt_const.mul analyticAt_id).cexp')
    have hχd : HasDerivAt χ (p * I) 0 := by
      simpa only [χ, id_eq, mul_zero, Complex.exp_zero, one_mul, mul_one] using
        ((((hasDerivAt_id (0 : ℂ)).const_mul I).cexp).const_mul p)
    refine ⟨χ, by simp only [χ, mul_zero, Complex.exp_zero, mul_one], hχa, ?_, ?_⟩
    · rw [hχd.deriv]
      exact mul_ne_zero hp0 I_ne_zero
    · apply Filter.Eventually.of_forall
      intro z
      rw [hfront, mem_sphere_zero_iff_norm]
      change ‖p * exp (I * z)‖ = 1 ↔ z.im = 0
      rw [norm_mul, hpn, one_mul, Complex.norm_exp, Real.exp_eq_one_iff]
      simp [Complex.mul_re]
end StructuralCrouzeix
end

end OAI
