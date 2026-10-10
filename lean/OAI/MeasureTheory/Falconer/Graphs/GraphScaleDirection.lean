import OAI.MeasureTheory.Falconer.Graphs.GraphDirectionStability
import OAI.MeasureTheory.Falconer.Geometry.InactiveBinScales

namespace OAI

namespace PlanarFalconer
open Set

theorem dyadic_direction_within_graph_scale {sig c s : ℝ}
    (hsig : 0 < sig) (hc : 0 < c) (hs : 0 ≤ s) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a p : ℝ, ∀ P Q : DyadicSquare,
    0 < P.side → 0 < Q.side → P.side ≤ s*(2 : ℝ)^(-p) → Q.side ≤ s*(2 : ℝ)^(-p) →
    ∀ x ∈ P.carrier, ∀ y ∈ Q.carrier, c*(2 : ℝ)^(-a) ≤ dist x y →
    Q.center ≠ P.center →
    dist (sourceRadialUnit x y) (sourceRadialUnit P.center Q.center) ≤
      graphUncappedAngularScale N sig (p-a) := by
  obtain ⟨N₀,h₀⟩ := fixed_constant_absorbed (by positivity : 0 < 10*sig) (8*s/c)
  refine ⟨N₀,?_⟩
  intro N hN a p P Q hP hQ hp hq x hx y hy hsep hcenter
  have hdist : 0 < dist x y := (mul_pos hc (Real.rpow_pos_of_pos (by norm_num) _)).trans_le hsep
  have hxy : y ≠ x := by intro he; simp [he] at hdist
  have h := dyadic_endpoint_direction_dist_le P Q hP hQ hx hy hxy hcenter
  have hnum : 4*(P.side+Q.side) ≤ 8*s*(2 : ℝ)^(-p) := by linarith
  have hb : 4*(P.side+Q.side)/dist x y ≤
      (8*s/c)*(2 : ℝ)^(-(p-a)) := by
    calc
      _ ≤ (8*s*(2 : ℝ)^(-p))/(c*(2 : ℝ)^(-a)) :=
        div_le_div₀ (by positivity) hnum (mul_pos hc (Real.rpow_pos_of_pos (by norm_num) _)) hsep
      _ = _ := by
        rw [show -(p-a) = -p-(-a) by ring, Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
        ring
  exact (h.trans hb).trans (by
    unfold graphUncappedAngularScale
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right (h₀ N hN)
      (Real.rpow_nonneg (by norm_num) (-(p-a))))

end PlanarFalconer

end OAI
