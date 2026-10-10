import OAI.MathematicalPhysics.Transonic.Profile.GlobalVelocity

namespace OAI

section
noncomputable section
namespace SepticProfile.SonicShooting
open Set Filter SourceFamily
open scoped Topology ContDiff

def MatchedPair.axisEven (M : MatchedPair) (x : ℝ) : ℝ :=
  (1-sonicSpeed/M.radius*M.axis.germ.realFunction M.parameter (x/M.radius^2))/
    (1-sonicSpeed/M.radius*x*M.axis.germ.realFunction M.parameter (x/M.radius^2))
def MatchedPair.radial (M : MatchedPair) (x : ℝ) : ℝ :=
  if x≤0 then M.axisEven x else M.velocity (Real.sqrt x)/Real.sqrt x

lemma MatchedPair.local_eq_axis {M : MatchedPair} {z : ℝ} (hz : z<M.axis.δ) :
    M.localProfile z=M.axisGerm z := by
  have he : z<endRadius M.sonic.e := by
    linarith [M.axis.δ_lt,(endRadius_bounds M.sonic.e_pos M.sonic.e_lt).1]
  exact (M.local_eventually_inner he).eq_of_nhds.trans (M.inner_eventually_axis hz).eq_of_nhds

lemma MatchedPair.velocity_axis {M : MatchedPair} {y : ℝ} (hy : y<M.radius*M.axis.δ) :
    M.velocity y=y*M.axisEven (y^2) := by
  unfold MatchedPair.velocity velocityToU MatchedPair.sonicU
  rw [M.local_eq_axis ((div_lt_iff₀ M.radius_bounds.1).mpr (by simpa only [mul_comm] using hy))]
  unfold MatchedPair.axisGerm AxisFamily.UniformGerm.velocity MatchedPair.axisEven
  rw [div_pow]
  have hn : y-sonicSpeed*(y/M.radius*M.axis.germ.realFunction M.parameter (y^2/M.radius^2))=
    y*(1-sonicSpeed/M.radius*M.axis.germ.realFunction M.parameter (y^2/M.radius^2)) := by ring
  have hd : 1-y*(sonicSpeed*(y/M.radius*M.axis.germ.realFunction M.parameter (y^2/M.radius^2)))=
    1-sonicSpeed/M.radius*y^2*M.axis.germ.realFunction M.parameter (y^2/M.radius^2) := by ring
  rw [hn,hd,mul_div_assoc]

lemma MatchedPair.axisEven_smooth_zero (M : MatchedPair) : ContDiffAt ℝ ∞ M.axisEven 0 := by
  have ha : ContDiffAt ℝ ∞ (fun x : ℝ => M.axis.germ.realFunction M.parameter (x/M.radius^2)) 0 := by
    apply ContDiffAt.comp (g:=M.axis.germ.realFunction M.parameter) 0 _ (contDiffAt_id.div_const _)
    simpa only [id_eq,zero_div] using (M.axis.germ.real_analytic M.parameter (by simpa only [abs_zero] using M.axis.germ.radius_pos : |(0:ℝ)|<M.axis.germ.radius)).contDiffAt
  unfold MatchedPair.axisEven
  apply (contDiffAt_const.sub (contDiffAt_const.mul ha)).div
    (contDiffAt_const.sub ((contDiffAt_const.mul contDiffAt_id).mul ha))
  simp

lemma MatchedPair.radial_eventually_axis (M : MatchedPair) : M.radial =ᶠ[𝓝 (0:ℝ)] M.axisEven := by
  have hb : 0<(M.radius*M.axis.δ)^2 := sq_pos_of_pos (mul_pos M.radius_bounds.1 M.axis.δ_pos)
  filter_upwards [Iio_mem_nhds hb] with x hx
  unfold MatchedPair.radial
  split_ifs with h
  · rfl
  · have hp : 0<x := lt_of_not_ge h
    have hs : Real.sqrt x<M.radius*M.axis.δ := by
      have he := Real.sq_sqrt hp.le
      have hn := Real.sqrt_nonneg x
      have hx' : x<(M.radius*M.axis.δ)^2 := hx
      have hpos := mul_pos M.radius_bounds.1 M.axis.δ_pos
      exact (sq_lt_sq₀ (Real.sqrt_nonneg x) hpos.le).mp (by rwa [he])
    rw [M.velocity_axis hs,Real.sq_sqrt hp.le]
    exact mul_div_cancel_left₀ _ (ne_of_gt (Real.sqrt_pos.mpr hp))

lemma MatchedPair.radial_smooth_zero (M : MatchedPair) : ContDiffAt ℝ ∞ M.radial 0 :=
  M.axisEven_smooth_zero.congr_of_eventuallyEq M.radial_eventually_axis

lemma PhysicalWidth.radial_smooth {M : MatchedPair} (W : PhysicalWidth M) {x : ℝ}
    (hx : x ∈ Icc (0:ℝ) (W.endpoint^2)) : ContDiffAt ℝ ∞ M.radial x := by
  by_cases hz : x=0
  · simpa only [hz] using M.radial_smooth_zero
  have hp : 0<x := lt_of_le_of_ne hx.1 (Ne.symm hz)
  have he : W.endpoint>0 := M.radius_bounds.1.trans W.endpoint_bounds.1
  have hs : Real.sqrt x≤W.endpoint := by
    exact (Real.sqrt_le_iff).mpr ⟨he.le,hx.2⟩
  have hv := W.velocity_smooth ⟨Real.sqrt_nonneg x,hs⟩
  have hf : ContDiffAt ℝ ∞ (fun t => M.velocity (Real.sqrt t)/Real.sqrt t) x :=
    (hv.comp x (Real.contDiffAt_sqrt hz)).div (Real.contDiffAt_sqrt hz) (ne_of_gt (Real.sqrt_pos.mpr hp))
  apply hf.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hp] with t ht
  exact ite_eq_right (not_le.mpr ht)

lemma MatchedPair.velocity_radial {M : MatchedPair} {y : ℝ} (hy : 0≤y) :
    M.velocity y=y*M.radial (y^2) := by
  by_cases hz : y=0
  · simp only [hz,zero_mul]
    rw [MatchedPair.velocity,M.sonicU_zero]
    norm_num [velocityToU]
  have hp : 0<y := lt_of_le_of_ne hy (Ne.symm hz)
  rw [MatchedPair.radial,ite_eq_right (not_le.mpr (sq_pos_of_pos hp)),Real.sqrt_sq hy]
  exact (mul_div_cancel₀ _ (ne_of_gt hp)).symm


end SepticProfile.SonicShooting

end
end

end OAI
