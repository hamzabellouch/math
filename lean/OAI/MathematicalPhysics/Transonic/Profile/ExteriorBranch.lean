import OAI.MathematicalPhysics.Transonic.Profile.ExteriorPhysicalSegment
import OAI.MathematicalPhysics.Transonic.Shooting.ExteriorGermEntry

namespace OAI

section
noncomputable section
namespace SepticProfile.SonicShooting
open Set SourceFamily ExteriorPolynomial

structure ExteriorBranch (M : MatchedPair) where
  width : PhysicalWidth M
  d : ℝ
  window : AdmissibleWindow (sig M.parameter) (kap M.parameter) d
    (SonicJet.jet (M.sonic.germ.realFunction M.parameter))
  a : ℝ
  a_pos : 0<a
  a_lt : a<1
  inside : d/256*a<width.w
  u : ℝ → ℝ
  start : u a=M.sonic.germ.realFunction M.parameter (d/256*a)
  bounds : ∀ x∈Icc a 1,
    (lowerPoly (SonicJet.jet (M.sonic.germ.realFunction M.parameter)) d).eval x≤u x ∧ u x<Real.sqrt (5/3)
  derivative : ∀ x∈Icc a 1, HasDerivWithinAt u
    (segmentField (sig M.parameter) (kap M.parameter) d (x,u x)) (Icc a 1) x

lemma MatchedPair.exists_exteriorBranch (M : MatchedPair)
    (hcert : (∃ d, AdmissibleWindow (sig M.parameter) (kap M.parameter) d
      (SonicJet.jet (M.sonic.germ.realFunction M.parameter))) ∧
      0<PowerSeries.coeff 74 (SonicJet.jet (M.sonic.germ.realFunction M.parameter))) :
    Nonempty (ExteriorBranch M) := by
  obtain ⟨d,W⟩ := hcert.1
  obtain ⟨width⟩ := M.exists_physicalWidth
  obtain ⟨a,ha,ha1,haw,har,haP,haq⟩ := M.sonic.germ.exists_exterior_entry M.parameter W.dpos width.pos hcert.2
  obtain ⟨u,hu,huc,hb,hd⟩ := exists_window_segment W (sigma_nonneg M.parameter) ha ha1.le haP.le haq
  exact ⟨⟨width,d,W,a,ha,ha1,haw,u,hu,hb,hd⟩⟩

def ExteriorBranch.beginning {M : MatchedPair} (B : ExteriorBranch M) : ℝ := location M.radius (B.d/256) B.a
def ExteriorBranch.endpoint {M : MatchedPair} (B : ExteriorBranch M) : ℝ := location M.radius (B.d/256) 1
def ExteriorBranch.velocity {M : MatchedPair} (B : ExteriorBranch M) : ℝ → ℝ := physicalSegment M.parameter B.d B.u

lemma ExteriorBranch.normalized_range {M : MatchedPair} (B : ExteriorBranch M) {x : ℝ}
    (hx : x∈Icc B.a 1) : 1<B.u x ∧ B.u x<Real.sqrt (5/3) :=
  ⟨(B.window.range x ⟨B.a_pos.trans_le hx.1,hx.2⟩).1.trans_le (B.bounds x hx).1,(B.bounds x hx).2⟩

lemma ExteriorBranch.beginning_bounds {M : MatchedPair} (B : ExteriorBranch M) :
    M.radius<B.beginning ∧ B.beginning<B.width.endpoint ∧ B.beginning<B.endpoint := by
  have hh : 0<B.d/256 := div_pos B.window.dpos (by norm_num)
  refine ⟨?_,?_,location_monotone M.radius_bounds.1 hh B.a_lt⟩
  · dsimp [ExteriorBranch.beginning,location]
    nlinarith [mul_pos hh B.a_pos,mul_pos M.radius_bounds.1 (mul_pos hh B.a_pos)]
  · dsimp [ExteriorBranch.beginning,location,PhysicalWidth.endpoint]
    exact mul_lt_mul_of_pos_left (by linarith [B.inside]) M.radius_bounds.1

lemma ExteriorBranch.endpoint_bounds {M : MatchedPair} (B : ExteriorBranch M) :
    0<B.endpoint ∧ B.endpoint<1 := by
  simpa only [ExteriorBranch.endpoint,location,mul_one,MatchedPair.radius,MatchedPair.beta] using PhysicalExterior.window_endpoint B.window

lemma ExteriorBranch.start_value {M : MatchedPair} (B : ExteriorBranch M) :
    B.velocity B.beginning=M.velocity B.beginning := by
  have hh : 0<B.d/256 := div_pos B.window.dpos (by norm_num)
  have hz : endRadius M.sonic.e<1+B.d/256*B.a := by
    have he := (endRadius_bounds M.sonic.e_pos M.sonic.e_lt).2
    nlinarith [mul_pos hh B.a_pos]
  have hr : B.beginning/M.radius=1+B.d/256*B.a := by
    unfold ExteriorBranch.beginning location
    rw [mul_div_cancel_left₀ _ (ne_of_gt M.radius_bounds.1)]
  change velocityToU B.beginning (sonicSpeed*B.u (coordinate M.radius (B.d/256) B.beginning))=
    velocityToU B.beginning (sonicSpeed*M.localProfile (B.beginning/M.radius))
  have hc : coordinate M.radius (B.d/256) B.beginning=B.a :=
    coordinate_location (ne_of_gt M.radius_bounds.1) (ne_of_gt hh) B.a
  rw [hc,B.start,hr,
    (M.local_eventually_germ hz).eq_of_nhds]
  simp only [Family.germArc,add_sub_cancel_left]

lemma ExteriorBranch.velocity_derivative {M : MatchedPair} (B : ExteriorBranch M) {y : ℝ}
    (hy : y∈Icc B.beginning B.endpoint) :
    HasDerivWithinAt B.velocity (PhysicalExterior.field ell M.beta (y,B.velocity y))
      (Icc B.beginning B.endpoint) y :=
  physical_segment_derivative B.window B.a_pos (fun _ hx => B.normalized_range hx) B.derivative hy

end SepticProfile.SonicShooting

end
end

end OAI
