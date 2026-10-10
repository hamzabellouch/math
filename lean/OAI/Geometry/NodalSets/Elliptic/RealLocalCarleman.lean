import OAI.Geometry.NodalSets.Elliptic.RealCarlemanEstimate
import OAI.Geometry.NodalSets.Elliptic.RealCarlemanWeight

namespace OAI

namespace Yau.Geometry
open Matrix Metric MeasureTheory
open scoped ContDiff
noncomputable section

theorem real_local_carleman (gamma potential psi : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgp : ∀ x, 0 < gamma x)
    (hpot : ContDiff ℝ ∞ potential)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hsym : ∀ x i j, B x i j = B x j i)
    (hpsi : ContDiff ℝ ∞ psi) (x0 : Yau.Jets.Coord)
    (hzero : psi x0 = 0) (hgrad : realCoordGradient psi x0 ≠ 0) (hpos : (B x0).PosDef) :
    ∃ K > 0, ∃ r > 0, ∃ a > 0, ∃ b > 0, ∃ T > 0,
      let phi := realConvexifiedPhase psi K
      ∀ v : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ v → HasCompactSupport v →
        tsupport v ⊆ ball x0 r → ∀ t : ℝ, T ≤ t →
          a*t*(∫ x, gamma x*realGradientSquare v x) + (b*t^3/4)*(∫ x, gamma x*v x^2) ≤
            (∫ x, gamma x*(Real.exp (t*phi x)*
              (realWeightedElliptic gamma B (fun y ↦ Real.exp (-t*phi y)*v y) x +
                potential x*(Real.exp (-t*phi x)*v x)))^2) := by
  obtain ⟨K,hK,s,hs,r,hr,a,ha,b,hb,C,hC,hlocal⟩ := real_carleman_weight_on_ball gamma hg
    (fun x ↦ (hgp x).ne') B hB hsym psi hpsi x0 hzero hgrad hpos
  let phi := realConvexifiedPhase psi K
  have hphi : ContDiff ℝ ∞ phi := realConvexifiedPhase_smooth psi hpsi K
  obtain ⟨M,hM,hMb⟩ := ((isCompact_closedBall x0 r).image hpot.continuous).isBounded.exists_pos_norm_le
  let T := max 1 ((C+s^2+4*M^2)/b)
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨K,hK,r,hr,a,ha,b,hb,T,hT,?_⟩
  dsimp only
  intro v hv hc hvs t ht
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 ≤ t := le_trans zero_le_one ht1
  have hbig : C+s^2+4*M^2 ≤ b*t := by
    have hh := (div_le_iff₀ hb).mp ((le_max_right _ _).trans ht)
    simpa only [mul_comm] using hh
  have hlarge : C+s^2 ≤ b*t := by nlinarith only [hbig,sq_nonneg M]
  have habs : 4*M^2 ≤ b*t^3 := by
    have hx := mul_nonneg hb.le (mul_nonneg (mul_nonneg ht0 (sub_nonneg.mpr ht1))
      (show 0 ≤ t+1 by positivity))
    nlinarith only [hbig,hx,sq_nonneg s,hC.le]
  have hpotB (x : Yau.Jets.Coord) (hx : x ∈ tsupport v) : (potential x)^2 ≤ M^2 := by
    have hbnd : |potential x| ≤ M := hMb _ ⟨x,mem_closedBall.mpr (mem_ball.mp (hvs hx)).le,rfl⟩
    nlinarith only [hbnd,abs_nonneg (potential x),hM.le,sq_abs (potential x)]
  have he := real_carleman_potential_estimate gamma phi v B hg hgp hB hsym hphi hv hc a b C s t
    hC.le ht1 hlarge (fun x hx ↦ (hlocal x (hvs hx)).1)
    (fun x hx ↦ (hlocal x (hvs hx)).2.1) (fun x hx ↦ (hlocal x (hvs hx)).2.2)
    potential hpot (M^2) hpotB habs
  have hexp (x : Yau.Jets.Coord) : Real.exp (t*phi x)*Real.exp (-t*phi x) = 1 := by
    rw [← Real.exp_add,show t*phi x + -t*phi x = 0 by ring,Real.exp_zero]
  have hid (x : Yau.Jets.Coord) : Real.exp (t*phi x)*
      (realWeightedElliptic gamma B (fun y ↦ Real.exp (-t*phi y)*v y) x +
        potential x*(Real.exp (-t*phi x)*v x)) =
      Real.exp (t*phi x)*realWeightedElliptic gamma B (fun y ↦ Real.exp (-t*phi y)*v y) x +
        potential x*v x := by
    linear_combination potential x*v x*hexp x
  change _ ≤ ∫ x, gamma x*(Real.exp (t*phi x)*
    (realWeightedElliptic gamma B (fun y ↦ Real.exp (-t*phi y)*v y) x +
      potential x*(Real.exp (-t*phi x)*v x)))^2
  simp_rw [hid]
  exact he

end
end Yau.Geometry

end OAI
