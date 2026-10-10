import OAI.Geometry.IsometricImmersion.Caps.CapFlowCoordinateJets

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def flowCoordinateBound (M : ℝ) : ℝ :=
  4 + Real.exp (2 * M) + 2 * M + M * Real.exp (2 * M) + 2 * M * Real.exp (4 * M) +
    (4 * M + 2 * M^2) + (2 * M + M^2) * Real.exp (2 * M) +
    (M + 2 * M^2) * Real.exp (4 * M) + (2 * M + 8 * M^2) * Real.exp (6 * M)

theorem flowCoordinateBound_dominates {M : ℝ} (hM : 0 ≤ M) :
    3 ≤ flowCoordinateBound M ∧ 1 ≤ flowCoordinateBound M ∧
    Real.exp (2 * M) ≤ flowCoordinateBound M ∧ 2 * M ≤ flowCoordinateBound M ∧
    M * Real.exp (2 * M) ≤ flowCoordinateBound M ∧ 2 * M * Real.exp (4 * M) ≤ flowCoordinateBound M ∧
    4 * M + 2 * M^2 ≤ flowCoordinateBound M ∧
    (2 * M + M^2) * Real.exp (2 * M) ≤ flowCoordinateBound M ∧
    (M + 2 * M^2) * Real.exp (4 * M) ≤ flowCoordinateBound M ∧
    (2 * M + 8 * M^2) * Real.exp (6 * M) ≤ flowCoordinateBound M := by
  have h1 : 0 ≤ Real.exp (2 * M) := (Real.exp_pos _).le
  have h2 : 0 ≤ 2 * M := by positivity
  have h3 : 0 ≤ M * Real.exp (2 * M) := by positivity
  have h4 : 0 ≤ 2 * M * Real.exp (4 * M) := by positivity
  have h5 : 0 ≤ 4 * M + 2 * M^2 := by positivity
  have h6 : 0 ≤ (2 * M + M^2) * Real.exp (2 * M) := by positivity
  have h7 : 0 ≤ (M + 2 * M^2) * Real.exp (4 * M) := by positivity
  have h8 : 0 ≤ (2 * M + 8 * M^2) * Real.exp (6 * M) := by positivity
  dsimp [flowCoordinateBound]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem flowCoordinateBound_nonneg {M : ℝ} (hM : 0 ≤ M) : 0 ≤ flowCoordinateBound M :=
  (by norm_num : (0 : ℝ) ≤ 3).trans (flowCoordinateBound_dominates hM).1

theorem coordinateProjection_partial (i j : Fin 2) :
    coordPartial i (fun p : Coord => p j) = (fun _ : Coord => (Pi.single i (1 : ℝ) : Coord) j) := by
  funext p
  unfold coordPartial
  rw [(hasFDerivAt_apply (𝕜 := ℝ) j p).fderiv]
  rfl

theorem coordinateProjection_bound (j : Fin 2) :
    CoordinateBound (fun p : Coord => p j) capChartDomain 3 3 := by
  intro ds hds p hp
  cases ds with
  | nil =>
    have hh : |p j| < 2 := by
      fin_cases j <;> simp only [Fin.mk_zero, Fin.mk_one]
      · exact abs_lt.mpr hp.1
      · exact abs_lt.mpr hp.2
    exact hh.le.trans (by norm_num)
  | cons i ds =>
    cases ds with
    | nil =>
      change |coordPartial i (fun p : Coord => p j) p| ≤ 3
      rw [coordinateProjection_partial]
      fin_cases i <;> fin_cases j <;> norm_num [Pi.single_apply]
    | cons k ds =>
      cases ds with
      | nil =>
        change |coordPartial i (coordPartial k (fun p : Coord => p j)) p| ≤ 3
        rw [coordinateProjection_partial]
        simp [coordPartial]
      | cons l ds =>
        cases ds with
        | nil =>
          change |coordPartial i (coordPartial k (coordPartial l (fun p : Coord => p j))) p| ≤ 3
          rw [coordinateProjection_partial]
          have hc : coordPartial k (fun _ : Coord => (Pi.single l (1 : ℝ) : Coord) j) =
              (fun _ : Coord => 0) := by
            funext x
            simp [coordPartial]
          rw [hc]
          simp [coordPartial]
        | cons m ds => simp only [List.length_cons] at hds; omega

section ActualFlow
variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ} {M : ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
variable (hM : 0 ≤ M)
variable (hq0 : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100)
variable (hq1 : ∀ i : Fin 2, ∀ p ∈ modelSquare, |coordPartial i q p| ≤ M)
variable (hq2 : ∀ i j : Fin 2, ∀ p ∈ modelSquare, |coordPartial i (coordPartial j q) p| ≤ M)
variable (hq3 : ∀ i j k : Fin 2, ∀ p ∈ modelSquare, |coordPartial i (coordPartial j (coordPartial k q)) p| ≤ M)
include hq hU hSU hY hrange hstart hode hM hq0 hq1 hq2 hq3

omit hq2 hq3 in
theorem capFlowHeight_word_one_bound
    (_ : ∀ first second : Fin 2, ∀ point ∈ modelSquare,
      |coordPartial first (coordPartial second q) point| ≤ M)
    (_ : ∀ first second third : Fin 2, ∀ point ∈ modelSquare,
      |coordPartial first (coordPartial second (coordPartial third q)) point| ≤ M)
    {p : Coord} (hp : p ∈ capChartDomain) (i : Fin 2) :
    |iteratedCoordPartial [i] (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
  have hs := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  obtain ⟨_, h1, hV, _⟩ := flowCoordinateBound_dominates hM
  fin_cases i <;> simp only [Fin.mk_zero, Fin.mk_one]
  · rw [show iteratedCoordPartial [0] (capFlowHeight Y) p = timeFlowDerivative Y (p 0, p 1) from
      capFlowHeight_partial_zero_eq hs hp]
    exact (cap_flow_time_bound hq hU hSU hY hrange hstart hode hq0 hp.2 hp.1).trans
      ((by norm_num : (1 : ℝ) / 100 ≤ 1).trans h1)
  · rw [show iteratedCoordPartial [1] (capFlowHeight Y) p = initialFlowDerivative Y (p 0, p 1) from
      capFlowHeight_partial_one_eq hs hp, initialFlowDerivative,
      abs_of_pos (cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hp.2 hp.1)]
    exact (cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM (hq1 1) hp.2 hp.1).2.trans hV

omit hq3 in
theorem capFlowHeight_word_two_bound
    (_ : ∀ first second third : Fin 2, ∀ point ∈ modelSquare,
      |coordPartial first (coordPartial second (coordPartial third q)) point| ≤ M)
    {p : Coord} (hp : p ∈ capChartDomain) (i j : Fin 2) :
    |iteratedCoordPartial [i, j] (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
  have hs := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hf := capFlowHeight_contDiffOn hs
  obtain ⟨_, _, _, htt, hts, hss, _⟩ := flowCoordinateBound_dominates hM
  have hqweak (p : Coord) (hp : p ∈ modelSquare) : |q p| ≤ 1 :=
    (hq0 p hp).trans (by norm_num)
  have h00 : |iteratedCoordPartial [0, 0] (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
    rw [capFlowHeight_word_00 hs hp]
    exact (cap_flow_time_second_bound hq hU hSU hY hrange hstart hode hM hqweak hq1 hp.2 hp.1).trans htt
  have h10 : |iteratedCoordPartial [1, 0] (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
    rw [capFlowHeight_word_10 hs hp]
    exact (cap_flow_mixed_bound hq hU hSU hY hrange hstart hode hM hq1 hp.2 hp.1).trans hts
  have h11 : |iteratedCoordPartial [1, 1] (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
    rw [capFlowHeight_word_11 hs hp]
    exact (cap_flow_initial_second_bound hq hU hSU hY hrange hstart hode hM (hq1 1) (hq2 1 1) hp.2 hp.1).trans hss
  fin_cases i <;> fin_cases j <;> simp only [Fin.mk_zero, Fin.mk_one]
  · exact h00
  · have he : iteratedCoordPartial [0, 1] (capFlowHeight Y) p = iteratedCoordPartial [1, 0] (capFlowHeight Y) p :=
      coordPartial_comm hf capChartDomain_isOpen hp 0 1
    rw [he]; exact h10
  · exact h10
  · exact h11

theorem capFlowHeight_word_three_bound {p : Coord} (hp : p ∈ capChartDomain) (i j k : Fin 2) :
    |iteratedCoordPartial [i, j, k] (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
  have hs := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hf := capFlowHeight_contDiffOn hs
  obtain ⟨_, _, _, _, _, _, httt, htts, htss, hsss⟩ := flowCoordinateBound_dominates hM
  have hqweak (p : Coord) (hp : p ∈ modelSquare) : |q p| ≤ 1 :=
    (hq0 p hp).trans (by norm_num)
  have h000 : |iteratedCoordPartial [0, 0, 0] (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
    rw [capFlowHeight_word_000 hs hp]
    exact (cap_flow_time_third_bound hq hU hSU hY hrange hstart hode hM hqweak hq1 hq2 hp.2 hp.1).trans httt
  have h100 : |iteratedCoordPartial [1, 0, 0] (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
    rw [capFlowHeight_word_100 hs hp]
    exact (cap_flow_time_second_initial_bound hq hU hSU hY hrange hstart hode hM hqweak hq1 hq2 hp.2 hp.1).trans htts
  have h110 : |iteratedCoordPartial [1, 1, 0] (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
    rw [capFlowHeight_word_110 hs hp]
    exact (cap_flow_mixed_initial_bound hq hU hSU hY hrange hstart hode hM hq1 hq2 hp.2 hp.1).trans htss
  have h111 : |iteratedCoordPartial [1, 1, 1] (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
    rw [capFlowHeight_word_111 hs hp]
    exact (cap_flow_initial_third_bound hq hU hSU hY hrange hstart hode hM (hq1 1) (hq2 1 1) (hq3 1 1 1) hp.2 hp.1).trans hsss
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp only [Fin.mk_zero, Fin.mk_one]
  · exact h000
  · rw [iterated_three_swap_inner hf capChartDomain_isOpen hp 0 0 1,
      iterated_three_swap_outer hf capChartDomain_isOpen hp 0 1 0]
    exact h100
  · rw [iterated_three_swap_outer hf capChartDomain_isOpen hp 0 1 0]
    exact h100
  · rw [iterated_three_swap_outer hf capChartDomain_isOpen hp 0 1 1,
      iterated_three_swap_inner hf capChartDomain_isOpen hp 1 0 1]
    exact h110
  · exact h100
  · rw [iterated_three_swap_inner hf capChartDomain_isOpen hp 1 0 1]
    exact h110
  · exact h110
  · exact h111

theorem capFlowHeight_coordinate_bound :
    CoordinateBound (capFlowHeight Y) capChartDomain 3 (flowCoordinateBound M) := by
  intro ds hds p hp
  cases ds with
  | nil =>
    have hh : |capFlowHeight Y p| ≤ 3 := abs_le.mpr
      (hrange (p 1) ⟨hp.2.1.le, hp.2.2.le⟩ (p 0) ⟨hp.1.1.le, hp.1.2.le⟩)
    exact hh.trans (flowCoordinateBound_dominates hM).1
  | cons i ds =>
    cases ds with
    | nil => exact capFlowHeight_word_one_bound hq hU hSU hY hrange hstart hode hM hq0 hq1 hq2 hq3 hp i
    | cons j ds =>
      cases ds with
      | nil => exact capFlowHeight_word_two_bound hq hU hSU hY hrange hstart hode hM hq0 hq1 hq2 hq3 hp i j
      | cons k ds =>
        cases ds with
        | nil => exact capFlowHeight_word_three_bound hq hU hSU hY hrange hstart hode hM hq0 hq1 hq2 hq3 hp i j k
        | cons l ds => simp only [List.length_cons] at hds; omega

theorem capChart_coefficient_coordinate_bound (j : Fin 2) :
    CoordinateBound (fun p => capChart Y p j) capChartDomain 3 (flowCoordinateBound M) := by
  fin_cases j <;> simp only [Fin.mk_zero, Fin.mk_one]
  · have he : (fun p => capChart Y p 0) = (fun p : Coord => p 0) := funext (capChart_zero Y)
    rw [he]
    exact (coordinateProjection_bound 0).mono le_rfl (flowCoordinateBound_dominates hM).1
  · have he : (fun p => capChart Y p 1) = capFlowHeight Y := funext (capChart_one Y)
    rw [he]
    exact capFlowHeight_coordinate_bound hq hU hSU hY hrange hstart hode hM hq0 hq1 hq2 hq3

end ActualFlow
end SmoothLocal.Flow

end

end OAI
