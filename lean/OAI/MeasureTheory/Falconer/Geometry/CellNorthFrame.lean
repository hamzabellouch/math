import OAI.MeasureTheory.Falconer.Geometry.MaskedGeometry
import OAI.MeasureTheory.Falconer.Angular.NorthRotation
import OAI.MeasureTheory.Falconer.Radial.RadialFreezing

namespace OAI

/-! # One angular frame for all pairs in separated original cells -/

namespace Falconer
open Set MeasureTheory NormedSpace

theorem separated_cells_north_frame (m : ℕ) (P Q : DyadicCube (m+3))
    (hP : 0 < P.side) (hQ : Q.side = P.side)
    (hsep : 125*(((m+3:ℕ):ℝ)+1)*P.side ≤ ‖P.center-Q.center‖) :
    ∃ T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3),
      ∀ x ∈ P.carrier, ∀ y ∈ Q.carrier,
        ‖T (normalize (x-y))-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8 := by
  have hs : 0 < 125*(((m+3:ℕ):ℝ)+1)*P.side := by positivity
  have hc : P.center-Q.center ≠ 0 := norm_pos_iff.mp (hs.trans_le hsep)
  let u : Sphere (m+3) := ⟨normalize (P.center-Q.center),by
    rw [Metric.mem_sphere,dist_zero_right,norm_normalize hc]⟩
  refine ⟨northRotation u,?_⟩
  intro x hx y hy
  have hpoints := P.separated_pairs_lower Q hP hQ hsep hx hy
  have hxy : x-y ≠ 0 := norm_pos_iff.mp
    ((show 0 < 100*(((m+3:ℕ):ℝ)+1)*P.side by positivity).trans_le hpoints)
  have hx' := P.dist_le hP.le (P.center_mem hP) hx
  have hy' := Q.dist_le (by rw [hQ]; exact hP.le) hy
    (Q.center_mem (by rw [hQ]; exact hP))
  rw [hQ] at hy'
  have hd : dist (P.center-Q.center) (x-y) ≤ 2*Real.sqrt (m+3:ℕ)*P.side := by
    rw [dist_eq_norm,show (P.center-Q.center)-(x-y) = (P.center-x)+(y-Q.center) by abel]
    exact (norm_add_le _ _).trans (by rw [← dist_eq_norm,← dist_eq_norm]; linarith)
  have hn := normalize_distance_scaled hsep hxy
  have hsmall : dist (normalize (x-y)) (normalize (P.center-Q.center)) ≤ 1/8 := by
    rw [dist_comm] at hn
    have hdim := mul_le_mul_of_nonneg_right (sqrt_dimension_le (m+3)) hP.le
    nlinarith
  rw [← linearIsometryEquiv_normalize_sub,northRotation_cap_norm]
  exact hsmall

end Falconer

end OAI
