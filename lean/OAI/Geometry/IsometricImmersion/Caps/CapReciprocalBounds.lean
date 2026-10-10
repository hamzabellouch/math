import OAI.Geometry.IsometricImmersion.Caps.CapFlowJetBounds

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem negative_over_cube_partial {f v : Coord → ℝ} {p : Coord}
    (hf : DifferentiableAt ℝ f p) (hv : DifferentiableAt ℝ v p) (hne : v p ≠ 0) (i : Fin 2) :
    coordPartial i (fun x => -f x / (v x)^3) p =
      -coordPartial i f p / (v p)^3 + 3 * f p * coordPartial i v p / (v p)^4 := by
  have hn : DifferentiableAt ℝ (fun x => -f x) p := hf.neg
  have hp : DifferentiableAt ℝ (fun x => (v x)^3) p := hv.pow 3
  rw [coordPartial_div hn hp (pow_ne_zero 3 hne) i]
  have hneg : coordPartial i (fun x => -f x) p = -coordPartial i f p := by simp [coordPartial]
  have hpow : coordPartial i (fun x => (v x)^3) p = 3 * (v p)^2 * coordPartial i v p := by
    unfold coordPartial
    rw [(hv.hasFDerivAt.pow 3).fderiv]
    norm_num [smul_apply, smul_eq_mul]
  rw [hneg, hpow]
  field_simp [hne]
  ring

theorem capChartRho_partial {Y : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (capFlowHeight Y) capChartDomain)
    {p : Coord} (hp : p ∈ capChartDomain)
    (hpos : 0 < coordPartial 1 (capFlowHeight Y) p) (i : Fin 2) :
    coordPartial i (capChartRho Y) p =
      -coordPartial i (coordPartial 1 (capFlowHeight Y)) p /
        (coordPartial 1 (capFlowHeight Y) p)^2 := by
  have hV := ((partial_contDiffOn hF capChartDomain_isOpen 1).contDiffAt
    (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp)
  change coordPartial i (fun x => (1 : ℝ) / coordPartial 1 (capFlowHeight Y) x) p = _
  rw [coordPartial_div (differentiableAt_const (1 : ℝ)) hV hpos.ne' i]
  simp [coordPartial]

theorem capChartSigma_partial {Y : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (capFlowHeight Y) capChartDomain)
    {p : Coord} (hp : p ∈ capChartDomain)
    (hpos : 0 < coordPartial 1 (capFlowHeight Y) p) (i : Fin 2) :
    coordPartial i (capChartSigma Y) p =
      -coordPartial i (coordPartial 1 (coordPartial 1 (capFlowHeight Y))) p /
        (coordPartial 1 (capFlowHeight Y) p)^3 +
      3 * coordPartial 1 (coordPartial 1 (capFlowHeight Y)) p *
        coordPartial i (coordPartial 1 (capFlowHeight Y)) p /
        (coordPartial 1 (capFlowHeight Y) p)^4 := by
  have hV := partial_contDiffOn hF capChartDomain_isOpen 1
  have hW := partial_contDiffOn hV capChartDomain_isOpen 1
  exact negative_over_cube_partial
    ((hW.contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp))
    ((hV.contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp)) hpos.ne' i

theorem capReciprocal_bounds_of_jets {Y : ℝ → ℝ → ℝ} {C c : ℝ}
    (hF : ContDiffOn ℝ ∞ (capFlowHeight Y) capChartDomain)
    (hC : 0 ≤ C) (hc : 0 < c)
    (hFB : CoordinateBound (capFlowHeight Y) capChartDomain 3 C)
    (hVlower : ∀ p ∈ capChartDomain, c ≤ coordPartial 1 (capFlowHeight Y) p)
    {p : Coord} (hp : p ∈ capChartDomain) :
    0 < capChartRho Y p ∧ |capChartRho Y p| ≤ 1 / c ∧
    (∀ i : Fin 2, |coordPartial i (capChartRho Y) p| ≤ C / c^2) ∧
    |capChartSigma Y p| ≤ C / c^3 ∧
    (∀ i : Fin 2, |coordPartial i (capChartSigma Y) p| ≤ C / c^3 + 3 * C^2 / c^4) := by
  have hVp : 0 < coordPartial 1 (capFlowHeight Y) p := hc.trans_le (hVlower p hp)
  have hpow (n : ℕ) : c^n ≤ |(coordPartial 1 (capFlowHeight Y) p)^n| := by
    rw [abs_pow, abs_of_pos hVp]
    exact pow_le_pow_left₀ hc.le (hVlower p hp) n
  have hW : |coordPartial 1 (coordPartial 1 (capFlowHeight Y)) p| ≤ C :=
    hFB [1, 1] (by norm_num) p hp
  have hVi (i : Fin 2) : |coordPartial i (coordPartial 1 (capFlowHeight Y)) p| ≤ C :=
    hFB [i, 1] (by norm_num) p hp
  have hWi (i : Fin 2) : |coordPartial i (coordPartial 1 (coordPartial 1 (capFlowHeight Y))) p| ≤ C :=
    hFB [i, 1, 1] (by norm_num) p hp
  refine ⟨one_div_pos.mpr hVp, ?_, ?_, ?_, ?_⟩
  · exact LowQuotient.abs_div_bound (by norm_num) (by norm_num : |(1 : ℝ)| ≤ 1) hc
      (by simpa only [abs_of_pos hVp] using hVlower p hp)
  · intro i
    rw [capChartRho_partial hF hp hVp i]
    exact LowQuotient.abs_div_bound hC (by simpa only [abs_neg] using hVi i)
      (pow_pos hc 2) (hpow 2)
  · exact LowQuotient.abs_div_bound hC (by simpa only [abs_neg] using hW)
      (pow_pos hc 3) (hpow 3)
  · intro i
    rw [capChartSigma_partial hF hp hVp i]
    have hfirst :
        |-coordPartial i (coordPartial 1 (coordPartial 1 (capFlowHeight Y))) p /
          (coordPartial 1 (capFlowHeight Y) p)^3| ≤ C / c^3 :=
      LowQuotient.abs_div_bound hC (by simpa only [abs_neg] using hWi i)
        (pow_pos hc 3) (hpow 3)
    have hnum : |3 * coordPartial 1 (coordPartial 1 (capFlowHeight Y)) p *
        coordPartial i (coordPartial 1 (capFlowHeight Y)) p| ≤ 3 * C^2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      calc
        _ = 3 * (|coordPartial 1 (coordPartial 1 (capFlowHeight Y)) p| *
            |coordPartial i (coordPartial 1 (capFlowHeight Y)) p|) := by ring
        _ ≤ 3 * (C * C) := mul_le_mul_of_nonneg_left
          (mul_le_mul hW (hVi i) (abs_nonneg _) hC) (by norm_num)
        _ = 3 * C^2 := by ring
    have hsecond := LowQuotient.abs_div_bound (by positivity) hnum (pow_pos hc 4) (hpow 4)
    exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

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

theorem capReciprocal_bounds_from_q {p : Coord} (hp : p ∈ capChartDomain) :
    0 < capChartRho Y p ∧ |capChartRho Y p| ≤ 1 / Real.exp (-2 * M) ∧
    (∀ i : Fin 2, |coordPartial i (capChartRho Y) p| ≤ flowCoordinateBound M / (Real.exp (-2 * M))^2) ∧
    |capChartSigma Y p| ≤ flowCoordinateBound M / (Real.exp (-2 * M))^3 ∧
    (∀ i : Fin 2, |coordPartial i (capChartSigma Y) p| ≤
      flowCoordinateBound M / (Real.exp (-2 * M))^3 +
        3 * (flowCoordinateBound M)^2 / (Real.exp (-2 * M))^4) := by
  have hs := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hVlower (x : Coord) (hx : x ∈ capChartDomain) :
      Real.exp (-2 * M) ≤ coordPartial 1 (capFlowHeight Y) x := by
    rw [capFlowHeight_partial_one_eq hs hx]
    exact (cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM (hq1 1) hx.2 hx.1).1
  exact capReciprocal_bounds_of_jets (capFlowHeight_contDiffOn hs) (flowCoordinateBound_nonneg hM)
    (Real.exp_pos _) (capFlowHeight_coordinate_bound hq hU hSU hY hrange hstart hode hM hq0 hq1 hq2 hq3)
    hVlower hp

end ActualFlow
end SmoothLocal.Flow

end

end OAI
