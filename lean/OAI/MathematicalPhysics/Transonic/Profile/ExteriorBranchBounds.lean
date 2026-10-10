import OAI.MathematicalPhysics.Transonic.Profile.WindowDenominator

namespace OAI

section
noncomputable section
namespace SepticProfile.SonicShooting
open Set SourceFamily ExteriorPolynomial PhysicalExterior

lemma ExteriorBranch.endpoint_eq {M : MatchedPair} (B : ExteriorBranch M) :
    B.endpoint=M.radius*(1+B.d/256) := by simp only [ExteriorBranch.endpoint,location,mul_one]

lemma ExteriorBranch.endpoint_value {M : MatchedPair} (B : ExteriorBranch M) :
    B.velocity B.endpoint=velocityToU B.endpoint (sonicSpeed*B.u 1) := by
  have hh : 0<B.d/256 := div_pos B.window.dpos (by norm_num)
  have hc : coordinate M.radius (B.d/256) B.endpoint=1 :=
    coordinate_location (ne_of_gt M.radius_bounds.1) (ne_of_gt hh) 1
  change velocityToU B.endpoint (sonicSpeed*B.u (coordinate M.radius (B.d/256) B.endpoint))=_
  rw [hc]

lemma ExteriorBranch.physical_range {M : MatchedPair} (B : ExteriorBranch M) {y : ℝ}
    (hy : y∈Icc B.beginning B.endpoint) :
    |B.velocity y|<1 ∧ B.velocity y<y ∧ y*B.velocity y<1 := by
  let x := coordinate M.radius (B.d/256) y
  have hh : 0<B.d/256 := div_pos B.window.dpos (by norm_num)
  have hx : x∈Icc B.a 1 := coordinate_mem M.radius_bounds.1 hh hy
  have hu := B.normalized_range hx
  have hup : 0<sonicSpeed*B.u x := mul_pos sonicSpeed_bounds.1 (by linarith only [hu.1])
  have hU : |sonicSpeed*B.u x|<1 := scaled_abs ⟨by linarith only [hu.1],hu.2⟩
  have hY := window_physical_bounds B.window B.a_pos hy
  have hv : |B.velocity y|<1 := velocityToU_range hY.2 hU
  have hp : 0<1-y*(sonicSpeed*B.u x) := by
    have hy1 := (abs_lt.mp hY.2).2
    have hv1 := (abs_lt.mp hU).2
    nlinarith only [hy1,mul_nonneg hY.1.le (sub_nonneg.mpr hv1.le)]
  refine ⟨hv,velocityToU_below hY.2 hup hp,?_⟩
  have hy1 := (abs_lt.mp hY.2).2
  have hv1 := (abs_lt.mp hv).2
  nlinarith only [hy1,mul_nonneg hY.1.le (sub_nonneg.mpr hv1.le)]

lemma ExteriorBranch.den_ne {M : MatchedPair} (B : ExteriorBranch M) {y : ℝ}
    (hy : y∈Icc B.beginning B.endpoint) : profileDenom ell y (B.velocity y)≠0 :=
  physical_segment_den_ne B.window B.a_pos (fun _ hx => B.normalized_range hx) hy

lemma ExteriorBranch.barrier_abs {M : MatchedPair} (B : ExteriorBranch M) :
    |velocityToU B.endpoint (sonicSpeed*(lowerPoly (SonicJet.jet (M.sonic.germ.realFunction M.parameter)) B.d).eval 1)|<1 := by
  have hY : |B.endpoint|<1 := by rw [abs_of_pos B.endpoint_bounds.1];exact B.endpoint_bounds.2
  have hP := B.window.range 1 ⟨by norm_num,le_rfl⟩
  have hq : (6/5:ℝ)<Real.sqrt (5/3) := by
    have he := Real.sq_sqrt (by norm_num : (0:ℝ)≤5/3)
    nlinarith only [he,Real.sqrt_nonneg (5/3:ℝ)]
  exact velocityToU_range hY (scaled_abs ⟨by linarith only [hP.1],hP.2.trans hq⟩)

end SepticProfile.SonicShooting

end
end

end OAI
