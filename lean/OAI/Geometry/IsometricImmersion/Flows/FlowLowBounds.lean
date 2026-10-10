import OAI.Geometry.IsometricImmersion.Flows.FlowTimeVariation

namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

private theorem abs_transport_bound {a b c M : ℝ} (hM : 0 ≤ M)
    (ha : |a| ≤ M) (hb : |b| ≤ M) (hc : |c| ≤ 1) :
    |a - c * b| ≤ 2 * M := by
  calc
    _ ≤ |a| + |c| * |b| := by simpa only [abs_mul] using abs_sub a (c * b)
    _ ≤ M + 1 * M := add_le_add ha (by
      simpa only [mul_comm] using mul_le_mul hb hc (abs_nonneg _) hM)
    _ = 2 * M := by ring

private theorem abs_second_initial_coefficient_bound {a b c d M : ℝ} (hM : 0 ≤ M)
    (ha : |a| ≤ M) (hb : |b| ≤ M) (hc : |c| ≤ 1) (hd : |d| ≤ M) :
    |-a + b * c + d^2| ≤ 2 * M + M^2 := by
  have hbase : |-a + b * c| ≤ 2 * M := by
    calc
      _ = |-(a - c * b)| := by congr 1; ring
      _ = |a - c * b| := abs_neg _
      _ ≤ 2 * M := abs_transport_bound hM ha hb hc
  have hsq : |d^2| ≤ M^2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hd 2
  exact (abs_add_le _ _).trans (add_le_add hbase hsq)

private theorem abs_third_time_coefficient_bound {a00 a10 a01 a11 a0 a1 c M : ℝ}
    (hM : 0 ≤ M) (hc : |c| ≤ 1)
    (h00 : |a00| ≤ M) (h10 : |a10| ≤ M) (h01 : |a01| ≤ M)
    (h11 : |a11| ≤ M) (h0 : |a0| ≤ M) (h1 : |a1| ≤ M) :
    |-a00 + c * a10 + (a01 - c * a11) * c + a1 * (a0 - c * a1)| ≤
      4 * M + 2 * M^2 := by
  have ha : |-a00 + c * a10| ≤ 2 * M := by
    calc
      _ = |-(a00 - c * a10)| := by congr 1; ring
      _ = |a00 - c * a10| := abs_neg _
      _ ≤ 2 * M := abs_transport_bound hM h00 h10 hc
  have hb := abs_transport_bound hM h01 h11 hc
  have hd := abs_transport_bound hM h0 h1 hc
  calc
    _ ≤ |-a00 + c * a10| + |a01 - c * a11| * |c| + |a1| * |a0 - c * a1| := by
      simpa only [abs_mul] using (abs_add_le (-a00 + c * a10 + (a01 - c * a11) * c)
        (a1 * (a0 - c * a1))).trans
          (add_le_add (abs_add_le (-a00 + c * a10) ((a01 - c * a11) * c)) le_rfl)
    _ ≤ 2 * M + (2 * M) * 1 + M * (2 * M) :=
      add_le_add (add_le_add ha (mul_le_mul hb hc (abs_nonneg _) (by positivity)))
        (mul_le_mul h1 hd (abs_nonneg _) hM)
    _ = 4 * M + 2 * M^2 := by ring

section ActualFlow
variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
include hq hU hSU hY hrange hstart hode

theorem cap_flow_time_bound
    (hq0 : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    |timeFlowDerivative Y (t, s)| ≤ (1 : ℝ) / 100 := by
  rw [timeFlowDerivative_eq hq hU hSU hY hrange hstart hode hs ht, abs_neg]
  exact hq0 _ (flowCoordinateMap_mem_modelSquare (p := (t, s)) hq hU hSU hY hrange hstart hode ⟨ht, hs⟩)

theorem cap_flow_time_second_bound {M : ℝ} (hM : 0 ≤ M)
    (hq0 : ∀ p ∈ modelSquare, |q p| ≤ 1)
    (hq1 : ∀ i : Fin 2, ∀ p ∈ modelSquare, |coordPartial i q p| ≤ M)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    |timeSecondFlowDerivative Y (t, s)| ≤ 2 * M := by
  rw [timeSecondFlowDerivative_eq hq hU hSU hY hrange hstart hode hs ht]
  have hp := flowCoordinateMap_mem_modelSquare (p := (t, s)) hq hU hSU hY hrange hstart hode ⟨ht, hs⟩
  have hh := abs_transport_bound hM (hq1 0 _ hp) (hq1 1 _ hp) (hq0 _ hp)
  calc
    _ = |-(coordPartial 0 q (coordinatePoint t (Y s t)) -
        q (coordinatePoint t (Y s t)) * coordPartial 1 q (coordinatePoint t (Y s t)))| := by
      congr 1; ring
    _ = |coordPartial 0 q (coordinatePoint t (Y s t)) -
        q (coordinatePoint t (Y s t)) * coordPartial 1 q (coordinatePoint t (Y s t))| := abs_neg _
    _ ≤ 2 * M := hh

theorem cap_flow_mixed_bound {M : ℝ} (hM : 0 ≤ M)
    (hq1 : ∀ i : Fin 2, ∀ p ∈ modelSquare, |coordPartial i q p| ≤ M)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    |mixedFlowDerivative Y (t, s)| ≤ M * Real.exp (2 * M) := by
  rw [mixedFlowDerivative_eq hq hU hSU hY hrange hstart hode hs ht, abs_mul, abs_neg, initialFlowDerivative,
    abs_of_pos (cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hs ht)]
  exact mul_le_mul (hq1 1 _
    (flowCoordinateMap_mem_modelSquare (p := (t, s)) hq hU hSU hY hrange hstart hode ⟨ht, hs⟩))
    (cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM (hq1 1) hs ht).2
    (cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hs ht).le hM

theorem cap_flow_mixed_initial_bound {M : ℝ} (hM : 0 ≤ M)
    (hq1 : ∀ i : Fin 2, ∀ p ∈ modelSquare, |coordPartial i q p| ≤ M)
    (hq2 : ∀ i j : Fin 2, ∀ p ∈ modelSquare, |coordPartial i (coordPartial j q) p| ≤ M)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    |deriv (fun u => mixedFlowDerivative Y (t, u)) s| ≤
      (M + 2 * M^2) * Real.exp (4 * M) := by
  rw [(cap_flow_mixed_initial_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).deriv]
  have hp := flowCoordinateMap_mem_modelSquare (p := (t, s)) hq hU hSU hY hrange hstart hode ⟨ht, hs⟩
  have hV := (cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM (hq1 1) hs ht).2
  have hVpos := cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hs ht
  have hVsq : |(initialFlowDerivative Y (t, s))^2| ≤ Real.exp (4 * M) := by
    rw [abs_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ (Real.exp (2 * M))^2 := pow_le_pow_left₀ hVpos.le hV 2
      _ = Real.exp (4 * M) := by rw [pow_two, ← Real.exp_add]; congr 1; ring
  have hW := cap_flow_initial_second_bound hq hU hSU hY hrange hstart hode hM (hq1 1) (hq2 1 1) hs ht
  calc
    _ ≤ |coordPartial 1 (coordPartial 1 q) (coordinatePoint t (Y s t))| *
        |(initialFlowDerivative Y (t, s))^2| +
        |coordPartial 1 q (coordinatePoint t (Y s t))| * |initialSecondFlowDerivative Y (t, s)| := by
      calc
        _ ≤ |-coordPartial 1 (coordPartial 1 q) (coordinatePoint t (Y s t)) *
            (initialFlowDerivative Y (t, s))^2| +
            |coordPartial 1 q (coordinatePoint t (Y s t)) * initialSecondFlowDerivative Y (t, s)| :=
          abs_sub _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_neg]
    _ ≤ M * Real.exp (4 * M) + M * (2 * M * Real.exp (4 * M)) :=
      add_le_add (mul_le_mul (hq2 1 1 _ hp) hVsq (abs_nonneg _) hM)
        (mul_le_mul (hq1 1 _ hp) hW (abs_nonneg _) hM)
    _ = (M + 2 * M^2) * Real.exp (4 * M) := by ring

theorem cap_flow_time_second_initial_bound {M : ℝ} (hM : 0 ≤ M)
    (hq0 : ∀ p ∈ modelSquare, |q p| ≤ 1)
    (hq1 : ∀ i : Fin 2, ∀ p ∈ modelSquare, |coordPartial i q p| ≤ M)
    (hq2 : ∀ i j : Fin 2, ∀ p ∈ modelSquare, |coordPartial i (coordPartial j q) p| ≤ M)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    |deriv (fun u => timeSecondFlowDerivative Y (t, u)) s| ≤
      (2 * M + M^2) * Real.exp (2 * M) := by
  rw [(cap_flow_time_second_initial_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).deriv,
    abs_mul, initialFlowDerivative, abs_of_pos (cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hs ht)]
  have hp := flowCoordinateMap_mem_modelSquare (p := (t, s)) hq hU hSU hY hrange hstart hode ⟨ht, hs⟩
  exact mul_le_mul
    (abs_second_initial_coefficient_bound hM (hq2 1 0 _ hp) (hq2 1 1 _ hp) (hq0 _ hp) (hq1 1 _ hp))
    (cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM (hq1 1) hs ht).2
    (cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hs ht).le (by positivity)

theorem cap_flow_time_third_bound {M : ℝ} (hM : 0 ≤ M)
    (hq0 : ∀ p ∈ modelSquare, |q p| ≤ 1)
    (hq1 : ∀ i : Fin 2, ∀ p ∈ modelSquare, |coordPartial i q p| ≤ M)
    (hq2 : ∀ i j : Fin 2, ∀ p ∈ modelSquare, |coordPartial i (coordPartial j q) p| ≤ M)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    |deriv (fun u => timeSecondFlowDerivative Y (u, s)) t| ≤ 4 * M + 2 * M^2 := by
  rw [(cap_flow_time_third_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).deriv]
  have hp := flowCoordinateMap_mem_modelSquare (p := (t, s)) hq hU hSU hY hrange hstart hode ⟨ht, hs⟩
  exact abs_third_time_coefficient_bound hM (hq0 _ hp)
    (hq2 0 0 _ hp) (hq2 1 0 _ hp) (hq2 0 1 _ hp) (hq2 1 1 _ hp)
    (hq1 0 _ hp) (hq1 1 _ hp)

end ActualFlow
end SmoothLocal.Flow

end

end OAI
