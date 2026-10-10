import OAI.MathematicalPhysics.Transonic.Profile.FiniteRadialProfile
import OAI.MathematicalPhysics.Transonic.Shooting.MatchedExistence

namespace OAI

noncomputable section

namespace SepticProfile.SonicShooting

open Set Filter SourceFamily
open scoped Topology ContDiff

theorem exists_finite_source_profile : ∃ (beta R : ℝ) (g : ℝ → ℝ),
    1<beta ∧ beta*(ell+Real.sqrt ell)<3 ∧
    0<sonicRadius beta ∧ sonicRadius beta<R ∧ R<1 ∧
    ContDiffOn ℝ ∞ g (Icc 0 (R^2)) ∧
    let v : ℝ → ℝ := fun y => y*g (y^2)
    (∀ y ∈ Icc (0:ℝ) R, |v y|<1) ∧
    (∀ y ∈ Icc (0:ℝ) R, profileDenom ell y (v y)*deriv v y=profileNumer ell beta y (v y)) ∧
    (∀ y ∈ Ioc (0:ℝ) R, v y<y ∧ y*v y<1) ∧
    (∀ y ∈ Icc (0:ℝ) R, velocityToU y (v y)=sonicSpeed ↔ y=sonicRadius beta) ∧
    0<deriv (fun y => velocityToU y (v y)) (sonicRadius beta) := by
  obtain ⟨M⟩ := exists_matched_pair
  obtain ⟨W⟩ := M.exists_physicalWidth
  refine ⟨M.beta,W.endpoint,M.radial,M.beta_bounds.1,M.beta_bounds.2,M.radius_bounds.1,
    W.endpoint_bounds.1,W.endpoint_bounds.2,fun x hx => (W.radial_smooth hx).contDiffWithinAt,?_⟩
  let v : ℝ → ℝ := fun y => y*M.radial (y^2)
  have hEq (y : ℝ) (hy : 0≤y) : v y=M.velocity y := (M.velocity_radial hy).symm
  have hNear (y : ℝ) (hy : 0<y) : v =ᶠ[𝓝 y] M.velocity := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact hEq t ht.le
  refine ⟨fun y hy => ?_,fun y hy => ?_,fun y hy => ?_,fun y hy => ?_,?_⟩
  · change |v y|<1
    rw [hEq y hy.1]
    exact W.velocity_abs hy
  · change profileDenom ell y (v y)*deriv v y=profileNumer ell M.beta y (v y)
    rw [hEq y hy.1]
    by_cases hz : y=0
    · subst y
      rw [MatchedPair.velocity,M.sonicU_zero]
      norm_num [velocityToU,profileDenom,profileNumer]
    · rw [(hNear y (lt_of_le_of_ne hy.1 (Ne.symm hz))).deriv_eq]
      exact W.velocity_equation hy
  · change v y<y ∧ y*v y<1
    rw [hEq y hy.1.le]
    exact W.velocity_below hy
  · change velocityToU y (v y)=sonicSpeed ↔ y=M.radius
    rw [hEq y hy.1]
    exact W.unique_sonic hy
  · change 0<deriv (fun y => velocityToU y (v y)) M.radius
    have hn : (fun y => velocityToU y (v y)) =ᶠ[𝓝 M.radius] (fun y => velocityToU y (M.velocity y)) := by
      filter_upwards [hNear M.radius M.radius_bounds.1] with y hy
      rw [hy]
    rw [hn.deriv_eq]
    exact W.sonic_slope


end SepticProfile.SonicShooting

end

end OAI
