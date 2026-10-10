import OAI.Geometry.NodalSets.Elliptic.RealConvexifiedQuadraticLemmas

namespace OAI

namespace Yau.Geometry
open Matrix
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

theorem positive_bilinear_shift
    (G D : Yau.Jets.Coord →L[ℝ] Yau.Jets.Coord →L[ℝ] ℝ)
    (hp : ∀ xi : Yau.Jets.Coord, xi ≠ 0 → 0 < G xi xi) :
    ∃ s > 0, ∀ xi : Yau.Jets.Coord, xi ≠ 0 → 0 < D xi xi+s*G xi xi := by
  obtain ⟨c,hc,C,hC,hbase⟩ := uniform_metric_coercivity (fun _ : Unit ↦ G) continuous_const (fun _ ↦ hp)
  let s := (‖D‖+1)/c
  have hs : 0 < s := by dsimp [s]; positivity
  have hsc : s*c = ‖D‖+1 := by dsimp [s]; field_simp
  refine ⟨s,hs,?_⟩
  intro xi hxi
  have hD : |D xi xi| ≤ ‖D‖*‖xi‖^2 := by
    simpa only [pow_two,mul_assoc] using bilinear_pairing_bound D xi xi
  have hG := mul_le_mul_of_nonneg_left ((hbase ()).2 xi) hs.le
  change s*(c*‖xi‖^2) ≤ s*G xi xi at hG
  rw [← mul_assoc,hsc] at hG
  have hlo := (abs_le.mp hD).1
  have hn : 0 < ‖xi‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hxi)
  nlinarith only [hG,hlo,hn]

theorem real_carleman_weight_at_point
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hsym : ∀ x i j, B x i j = B x j i)
    (psi : Yau.Jets.Coord → ℝ) (hpsi : ContDiff ℝ ∞ psi)
    (x0 : Yau.Jets.Coord) (hzero : psi x0 = 0) (hgrad : realCoordGradient psi x0 ≠ 0)
    (hpos : (B x0).PosDef) :
    ∃ K > 0, ∃ s > 0,
      (∀ xi : Yau.Jets.Coord, xi ≠ 0 →
        0 < realTransportQuadratic B (realMatrixFlux B (realConvexifiedPhase psi K)) x0 xi +
          s*coordMatrixForm (B x0) xi xi) ∧
      0 < Yau.pairing (realMatrixEnergy B (realConvexifiedPhase psi K) (realConvexifiedPhase psi K))
        (realMatrixFlux B (realConvexifiedPhase psi K)) x0 -
        s*realMatrixEnergy B (realConvexifiedPhase psi K) (realConvexifiedPhase psi K) x0 := by
  obtain ⟨s,hs,hshift⟩ := positive_bilinear_shift (coordMatrixForm (B x0))
    (realTransportBilinear B (realMatrixFlux B psi) x0) (coordMatrixForm_positive (B x0) hpos)
  let q := realMatrixEnergy B psi psi x0
  let P := Yau.pairing (realMatrixEnergy B psi psi) (realMatrixFlux B psi) x0
  have hq : 0 < q := coordMatrixForm_positive (B x0) hpos _ hgrad
  let K := (|P-s*q|+1)/(4*q^2)
  have hK : 0 < K := by dsimp [K]; positivity
  have hKq : 4*K*q^2 = |P-s*q|+1 := by dsimp [K]; field_simp
  refine ⟨K,hK,s,hs,?_,?_⟩
  · intro xi hxi
    rw [real_convexified_quadratic B hB hsym psi hpsi K x0 hzero]
    have hh := hshift xi hxi
    rw [realTransportBilinear_diagonal] at hh
    have hnon := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hK.le)
      (sq_nonneg (∑ k, realMatrixFlux B psi x0 k*xi k))
    linarith only [hh,hnon]
  · rw [real_convexified_cubic B hB psi hpsi K x0 hzero,realMatrixEnergy_convexified B psi hpsi,
      hzero,mul_zero,add_zero,one_pow,one_mul]
    change 0 < P+4*K*q^2-s*q
    rw [hKq]
    have hh := neg_abs_le (P-s*q)
    linarith only [hh]

theorem real_carleman_weight_on_ball (gamma : Yau.Jets.Coord → ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hsym : ∀ x i j, B x i j = B x j i)
    (psi : Yau.Jets.Coord → ℝ) (hpsi : ContDiff ℝ ∞ psi)
    (x0 : Yau.Jets.Coord) (hzero : psi x0 = 0) (hgrad : realCoordGradient psi x0 ≠ 0)
    (hpos : (B x0).PosDef) :
    ∃ K > 0, ∃ s > 0, ∃ r > 0, ∃ a > 0, ∃ b > 0, ∃ C > 0,
      ∀ x ∈ Metric.ball x0 r,
        (∀ xi : Yau.Jets.Coord, a*(∑ i, (xi i)^2) ≤
          realTransportQuadratic B (realMatrixFlux B (realConvexifiedPhase psi K)) x xi +
          s*coordMatrixForm (B x) xi xi) ∧
        b ≤ Yau.pairing (realMatrixEnergy B (realConvexifiedPhase psi K) (realConvexifiedPhase psi K))
          (realMatrixFlux B (realConvexifiedPhase psi K)) x -
          s*realMatrixEnergy B (realConvexifiedPhase psi K) (realConvexifiedPhase psi K) x ∧
        realWeightedElliptic gamma B (realWeightedElliptic gamma B (realConvexifiedPhase psi K)) x ≤ C := by
  obtain ⟨K,hK,s,hs,hQ,hW⟩ := real_carleman_weight_at_point B hB hsym psi hpsi x0 hzero hgrad hpos
  have hphi := realConvexifiedPhase_smooth psi hpsi K
  obtain ⟨r,hr,a,ha,b,hb,C,hC,hlocal⟩ := real_carleman_local_conditions gamma
    (realMatrixEnergy B (realConvexifiedPhase psi K) (realConvexifiedPhase psi K)) B
    (realMatrixFlux B (realConvexifiedPhase psi K)) hg hgn
    (realMatrixEnergy_smooth B hB _ _ hphi hphi) hB (realMatrixFlux_smooth B _ hB hphi) x0 s hQ hW
  exact ⟨K,hK,s,hs,r,hr,a,ha,b,hb,C,hC,hlocal⟩

end
end Yau.Geometry

end OAI
