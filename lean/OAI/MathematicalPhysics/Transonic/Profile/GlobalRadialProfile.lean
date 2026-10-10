import OAI.MathematicalPhysics.Transonic.Profile.FiniteRadialProfile
import OAI.MathematicalPhysics.Transonic.Profile.Existence

namespace OAI

section
noncomputable section
namespace SepticProfile.SonicShooting
open Set Filter SourceFamily
open scoped Topology ContDiff

def ExteriorTail.radial {M : MatchedPair} {B : ExteriorBranch M} (T : ExteriorTail B) (x : ℝ) : ℝ :=
  if x≤0 then M.axisEven x else T.globalVelocity (Real.sqrt x)/Real.sqrt x

lemma ExteriorTail.global_zero {M : MatchedPair} {B : ExteriorBranch M} (T : ExteriorTail B) :
    T.globalVelocity 0=0 := by
  rw [(T.global_near_local (M.radius_bounds.1.trans B.beginning_bounds.1)).eq_of_nhds,
    MatchedPair.velocity,M.sonicU_zero]
  norm_num [velocityToU]

lemma ExteriorTail.radial_eventually_axis {M : MatchedPair} {B : ExteriorBranch M} (T : ExteriorTail B) :
    T.radial =ᶠ[𝓝 (0:ℝ)] M.axisEven := by
  have hb : 0<(M.radius*M.axis.δ)^2 := sq_pos_of_pos (mul_pos M.radius_bounds.1 M.axis.δ_pos)
  have hδ : M.radius*M.axis.δ<B.beginning := by
    have he : M.radius*M.axis.δ<M.radius := by
      apply mul_lt_of_lt_one_right M.radius_bounds.1
      linarith only [M.axis.δ_lt]
    exact he.trans B.beginning_bounds.1
  filter_upwards [Iio_mem_nhds hb] with x hx
  unfold ExteriorTail.radial
  split_ifs with h
  · rfl
  · have hp : 0<x := lt_of_not_ge h
    have hs : Real.sqrt x<M.radius*M.axis.δ := by
      exact (sq_lt_sq₀ (Real.sqrt_nonneg x) (mul_pos M.radius_bounds.1 M.axis.δ_pos).le).mp
        (by rwa [Real.sq_sqrt hp.le])
    rw [(T.global_near_local (hs.trans hδ)).eq_of_nhds,M.velocity_axis hs,Real.sq_sqrt hp.le]
    exact mul_div_cancel_left₀ _ (ne_of_gt (Real.sqrt_pos.mpr hp))

lemma ExteriorTail.radial_smooth {M : MatchedPair} {B : ExteriorBranch M} (T : ExteriorTail B)
    {x : ℝ} (hx : 0≤x) : ContDiffAt ℝ ∞ T.radial x := by
  by_cases hz : x=0
  · subst x
    exact M.axisEven_smooth_zero.congr_of_eventuallyEq T.radial_eventually_axis
  have hp : 0<x := lt_of_le_of_ne hx (Ne.symm hz)
  have hv := T.global_smooth (Real.sqrt_nonneg x)
  have hf : ContDiffAt ℝ ∞ (fun t => T.globalVelocity (Real.sqrt t)/Real.sqrt t) x :=
    (hv.comp x (Real.contDiffAt_sqrt hz)).div (Real.contDiffAt_sqrt hz) (ne_of_gt (Real.sqrt_pos.mpr hp))
  apply hf.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hp] with t ht
  exact ite_eq_right (not_le.mpr ht)

lemma ExteriorTail.velocity_radial {M : MatchedPair} {B : ExteriorBranch M} (T : ExteriorTail B)
    {y : ℝ} (hy : 0≤y) : T.globalVelocity y=y*T.radial (y^2) := by
  by_cases hz : y=0
  · simp only [hz,zero_mul,T.global_zero]
  have hp : 0<y := lt_of_le_of_ne hy (Ne.symm hz)
  rw [ExteriorTail.radial,ite_eq_right (not_le.mpr (sq_pos_of_pos hp)),Real.sqrt_sq hy]
  exact (mul_div_cancel₀ _ (ne_of_gt hp)).symm

theorem ExteriorTail.relativistic_profile {M : MatchedPair} {B : ExteriorBranch M} (T : ExteriorTail B) :
    RelativisticProfileExists := by
  refine ⟨M.beta,T.radial,M.beta_bounds.1,M.beta_bounds.2,
    fun x hx => (T.radial_smooth hx).contDiffWithinAt,?_⟩
  let v : ℝ → ℝ := fun y => y*T.radial (y^2)
  have hEq (y : ℝ) (hy : 0≤y) : v y=T.globalVelocity y := (T.velocity_radial hy).symm
  have hNear (y : ℝ) (hy : 0<y) : v =ᶠ[𝓝 y] T.globalVelocity := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact hEq t ht.le
  refine ⟨fun y hy => ?_,fun y hy => ?_,fun y hy => ?_,M.radius_bounds.1,M.radius_bounds.2,
    fun y hy => ?_,?_⟩
  · change |v y|<1
    rw [hEq y hy]
    exact T.global_range hy
  · change profileDenom ell y (v y)*deriv v y=profileNumer ell M.beta y (v y)
    rw [hEq y hy]
    by_cases hz : y=0
    · subst y
      rw [T.global_zero]
      norm_num [profileDenom,profileNumer]
    · rw [(hNear y (lt_of_le_of_ne hy (Ne.symm hz))).deriv_eq]
      exact T.global_equation hy
  · change v y<y ∧ y*v y<1
    rw [hEq y hy.le]
    exact T.global_below hy
  · change velocityToU y (v y)=sonicSpeed ↔ y=M.radius
    rw [hEq y hy]
    exact T.global_unique_sonic hy
  · change 0<deriv (fun y => velocityToU y (v y)) M.radius
    have hn : (fun y => velocityToU y (v y)) =ᶠ[𝓝 M.radius]
        (fun y => velocityToU y (T.globalVelocity y)) := by
      filter_upwards [hNear M.radius M.radius_bounds.1] with y hy
      rw [hy]
    rw [hn.deriv_eq]
    exact T.global_sonic_slope

end SepticProfile.SonicShooting

end
end

end OAI
