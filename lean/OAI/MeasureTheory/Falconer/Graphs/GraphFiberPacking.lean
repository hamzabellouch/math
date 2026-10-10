import OAI.MeasureTheory.Falconer.Recursion.ProductRetainedStrip
import OAI.MeasureTheory.Falconer.Geometry.ScaledDyadicPacking

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

theorem graphB_norm_exact (z : ℝ) (v : Plane) :
    ‖graphB z v‖ = (Real.sqrt (1+z^2)/2)*‖v‖ := by
  have he : quarterTurn (v+z • quarterTurn v) = quarterTurn v+(-z) • v := by
    ext l
    fin_cases l <;> simp [quarterTurn]
    ring
  have hn : ‖v+z • quarterTurn v‖ = Real.sqrt (1+z^2)*‖v‖ := by
    rw [← graph_quarterTurn_norm (v+z • quarterTurn v),he,norm_quarterTurn_add,neg_sq]
  rw [graphB,norm_smul,hn,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
  ring

theorem graphB_inverse_norm_le (z : ℝ) (v : Plane) : ‖v‖ ≤ 2*‖graphB z v‖ := by
  rw [graphB_norm_exact]
  have hs : 1 ≤ Real.sqrt (1+z^2) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith [sq_nonneg z]
  calc
    ‖v‖ = 1*‖v‖ := (one_mul _).symm
    _ ≤ Real.sqrt (1+z^2)*‖v‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg v)
    _ = 2*((Real.sqrt (1+z^2)/2)*‖v‖) := by ring

theorem graphA_inverse_norm_le (z : ℝ) (v : Plane) : ‖v‖ ≤ 2*‖graphA z v‖ := by
  simpa only [graphB,graphA,neg_smul,← sub_eq_add_neg] using graphB_inverse_norm_le (-z) v

theorem graphB_two_edges_close (z s S : ℝ) (v w w' : Plane) (hs : s = 1 ∨ s = -1)
    (h : ‖graphA z v+s • graphB z w‖ ≤ S)
    (h' : ‖graphA z v+s • graphB z w'‖ ≤ S) : dist w w' ≤ 4*S := by
  have he : (graphA z v+s • graphB z w)-(graphA z v+s • graphB z w') = s • graphB z (w-w') := by
    ext l
    fin_cases l <;> simp [graphB,quarterTurn] <;> ring
  have hn : ‖s • graphB z (w-w')‖ = ‖graphB z (w-w')‖ := by
    rcases hs with rfl | rfl <;> simp
  have hb := (norm_sub_le (graphA z v+s • graphB z w) (graphA z v+s • graphB z w')).trans (add_le_add h h')
  rw [he,hn] at hb
  have hl := graphB_inverse_norm_le z (w-w')
  rw [dist_eq_norm]
  linarith

theorem graphA_two_edges_close (z s S : ℝ) (v v' w : Plane)
    (h : ‖graphA z v+s • graphB z w‖ ≤ S)
    (h' : ‖graphA z v'+s • graphB z w‖ ≤ S) : dist v v' ≤ 4*S := by
  have he : (graphA z v+s • graphB z w)-(graphA z v'+s • graphB z w) = graphA z (v-v') := by
    ext l
    fin_cases l <;> simp [graphA,quarterTurn] <;> ring
  have hb := (norm_sub_le (graphA z v+s • graphB z w) (graphA z v'+s • graphB z w)).trans (add_le_add h h')
  rw [he] at hb
  have hl := graphA_inverse_norm_le z (v-v')
  rw [dist_eq_norm]
  linarith

theorem graph_unit_center_fiber_card (Q : DyadicSquare) (hQ : Q.side = 1)
    (N p : ℕ) {sig : ℝ} (hsig : 0 ≤ sig) (S : Finset CellPath) (hS : S ⊆ dyadicPaths p)
    (x : Plane) (hb : ∀ c ∈ S, dist (Q.descendant c).center x ≤ 4*graphNonedgeThreshold N sig p) :
    (S.card : ℝ) ≤ 144*((2:ℝ)^N)^(60*sig) := by
  classical
  have hQpos : 0 < Q.side := by rw [hQ]; norm_num
  have hpos : 0 < graphNonedgeThreshold N sig p := by unfold graphNonedgeThreshold; positivity
  have hsub : S ⊆ cellsMeeting Q p x (5*graphNonedgeThreshold N sig p) := by
    intro c hc
    apply Finset.mem_filter.mpr
    refine ⟨hS hc,(Q.descendant c).center,(Q.descendant c).center_mem (Q.descendant_side_pos hQpos c),?_⟩
    exact (hb c hc).trans_lt (by linarith)
  have hp := dyadic_scaled_ball_card_le Q hQpos p x
    (C₀ := 5*((2:ℝ)^N)^(30*sig)) (by positivity) (r := 5*graphNonedgeThreshold N sig p) (by
      rw [hQ,graphNonedgeThreshold,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast]
      exact le_of_eq (by ring))
  have hR : 1 ≤ ((2:ℝ)^N)^(30*sig) := Real.one_le_rpow (one_le_pow₀ (by norm_num)) (by positivity)
  have he : (((2:ℝ)^N)^(30*sig))^2 = ((2:ℝ)^N)^(60*sig) := by
    rw [← Real.rpow_natCast _ 2,← Real.rpow_mul (by positivity : (0:ℝ) ≤ (2:ℝ)^N)]
    congr 1
    ring
  have hsquare : 4*(5*((2:ℝ)^N)^(30*sig)+1)^2 ≤ 144*(((2:ℝ)^N)^(30*sig))^2 := by
    nlinarith [sq_nonneg (((2:ℝ)^N)^(30*sig)-1)]
  rw [he] at hsquare
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hp.trans hsquare)

end PlanarFalconer

end OAI
