import OAI.Geometry.RCD.Heat.HeatMeasureMassContinuity

namespace OAI

/-! # Conservation of the constructed heat measures

Semigroup self-adjointness passes compact cutoff exhaustion through the
heat flow. Its already proved L¹ mass conservation then forces the mass
of the pointwise Radon measures to be one at every center.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology CompactlySupported

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

omit [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] in
theorem compactHeatEval_continuous (t : ℝ) (ht : 0 < t) (f : C_c(X, ℝ)) :
    Continuous (fun x => hX.compactHeatEval hn p t ht x f) :=
  hX.boundedHeat_continuous hn p (compactTestToL2 (hausdorff n X) f)
    (compactTestToL2_bounded f) t ht

omit [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] in
theorem compactHeatEval_pair (t : ℝ) (ht : 0 < t) (F G : C_c(X, ℝ)) :
    (∫ x, F x * hX.compactHeatEval hn p t ht x G ∂hausdorff n X) =
      ∫ x, heatAt (hausdorff n X) hX.quadratic t
        (compactTestToL2 (hausdorff n X) F) x * G x ∂hausdorff n X := by
  let μ := hausdorff n X
  calc
    _ = inner ℝ (compactTestToL2 μ F) (heatAt μ hX.quadratic t (compactTestToL2 μ G)) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [compactTestToL2_coe μ F,
        hX.boundedHeat_represents hn p (compactTestToL2 μ G) (compactTestToL2_bounded G) t ht]
        with x hx hy
      simp only [Real.inner_apply, hx]
      exact congrArg (fun a => F x * a) hy.symm
    _ = inner ℝ (heatAt μ hX.quadratic t (compactTestToL2 μ F)) (compactTestToL2 μ G) :=
      (heatAt_inner μ hX.quadratic t _ _).symm
    _ = _ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [compactTestToL2_coe μ G] with x hx
      simp only [Real.inner_apply, hx, μ]

/-- Averaging total pointwise mass against any nonnegative compact test
recovers exactly that test's reference integral. -/
theorem heatRadonMeasure_mass_average (t : ℝ) (ht : 0 < t)
    (F : C_c(X, ℝ)) (hF : ∀ x, 0 ≤ F x) :
    (∫ x, F x * (hX.heatRadonMeasure hn p t ht x).real univ ∂hausdorff n X) =
      ∫ x, F x ∂hausdorff n X := by
  let μ := hausdorff n X
  let U := compactTestToL2 μ F
  let G (i : ℕ) := radialCompactTest p ((i : ℝ) + 1) (by positivity)
  have hbound (i : ℕ) (x : X) : |hX.compactHeatEval hn p t ht x (G i)| ≤ 1 :=
    hX.compactHeatEval_abs_le hn p t ht x (G i) 1 (fun y => by
      change |radialCutoff p ((i : ℝ) + 1) y| ≤ 1
      rw [abs_of_nonneg (radialCutoff_bounds _ _ _).1]
      exact (radialCutoff_bounds _ _ _).2)
  have hleft : Tendsto (fun i => ∫ x, F x * hX.compactHeatEval hn p t ht x (G i) ∂μ)
      atTop (𝓝 (∫ x, F x * (hX.heatRadonMeasure hn p t ht x).real univ ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => |F x|)
    · intro i
      exact (F.continuous.mul (hX.compactHeatEval_continuous hn p t ht (G i))).aestronglyMeasurable
    · exact F.integrable.abs
    · intro i
      filter_upwards with x
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) (hbound i x)
    · filter_upwards with x
      exact tendsto_const_nhds.mul (hX.heatRadonMeasure_mass_limit hn p t ht x)
  have hUi : Integrable U μ := F.integrable.congr (compactTestToL2_coe μ F).symm
  have hPi := heatAt_integrable μ hX.quadratic t U hUi
  have hr : Tendsto (fun i : ℕ => (i : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hright := (integral_radialCutoff_tendsto μ p _ hPi).comp hr
  have heq (i : ℕ) := hX.compactHeatEval_pair hn p t ht F (G i)
  have hright' : Tendsto (fun i => ∫ x, F x * hX.compactHeatEval hn p t ht x (G i) ∂μ)
      atTop (𝓝 (∫ x, heatAt μ hX.quadratic t U x ∂μ)) := by
    have heqfun : (fun i => ∫ x, F x * hX.compactHeatEval hn p t ht x (G i) ∂μ) =
        (fun i : ℕ => ∫ x, heatAt μ hX.quadratic t U x * radialCutoff p ((i : ℝ) + 1) x ∂μ) := by
      funext i
      exact heq i
    rw [heqfun]
    simpa only [Function.comp_def] using! hright
  have hu0 : 0 ≤ U := (Lp.coeFn_nonneg _).mp (by
    filter_upwards [compactTestToL2_coe μ F] with x hx
    rw [hx]
    exact hF x)
  obtain ⟨A, B, hA, hB, hvol⟩ := hX.exponential_volume K n hn p
  have hmass := heatAt_integral_eq_of_exponential_volume μ hX.quadratic p hA hB hvol U hu0 hUi ht.le
  exact (tendsto_nhds_unique hleft hright').trans
    (hmass.trans (integral_congr_ae (compactTestToL2_coe μ F)))

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
