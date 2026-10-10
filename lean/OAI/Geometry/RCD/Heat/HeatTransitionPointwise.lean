import OAI.Geometry.RCD.Heat.HeatTransitionDecay

namespace OAI

/-! # Pointwise bounds for actual heat transition probabilities

Spatial strong Feller smoothing converts the separated-set Davies estimate
to a bound at each starting point. The localization radius remains free,
so it can be optimized later using the established volume comparison.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem heatRadonMeasure_set_lipschitz (t : ℝ) (ht : 0 < t)
    {A : Set X} (hA : MeasurableSet A) :
    LipschitzWith ⟨Real.sqrt (1 / (2*t*Real.exp (-2*|K| * t))), Real.sqrt_nonneg _⟩
      (fun x => (hX.heatRadonMeasure hn p t ht x).real A) := by
  have hm : Measurable (A.indicator (fun _ : X => (1 : ℝ))) := measurable_const.indicator hA
  have hb (x : X) : |A.indicator (fun _ : X => (1 : ℝ)) x| ≤ (1 : ℝ≥0) := by
    by_cases hx : x ∈ A <;> simp [hx]
  have h := hX.heatRadonMeasure_integral_measurable_lipschitz hn p t ht _ hm 1 hb
  simpa only [integral_indicator hA, integral_const, smul_eq_mul, mul_one,
    NNReal.coe_one, one_pow, measureReal_restrict_apply MeasurableSet.univ, univ_inter] using! h

/-- A pointwise transition bound derived without a pointwise kernel estimate. -/
theorem heatRadonMeasure_pointwise_separated (t : ℝ) (ht : 0 < t)
    {A : Set X} (hA : MeasurableSet A) (hAf : hausdorff n X A ≠ ∞)
    (q x : X) {r δ : ℝ} (hδ : 0 < δ) (hsep : r + δ ≤ dist q x)
    (hnear : ∀ y ∈ A, dist q y ≤ r) :
    (hX.heatRadonMeasure hn p t ht x).real A ≤
      Real.sqrt (1 / (2*t*Real.exp (-2*|K| * t))) * δ +
        Real.exp (-((dist q x-δ)-r)^2 / (4*t)) * Real.sqrt ((hausdorff n X).real A) /
          Real.sqrt ((hausdorff n X).real (ball x δ)) := by
  let μ := hausdorff n X
  let v (y : X) := (hX.heatRadonMeasure hn p t ht y).real A
  let L := Real.sqrt (1 / (2*t*Real.exp (-2*|K| * t)))
  let V := μ.real (ball x δ)
  have hV : 0 < V := ENNReal.toReal_pos (hX.fullSupport x δ hδ).ne'
    (hX.finiteOnBounded _ isBounded_ball).ne
  let : IsFiniteMeasure (μ.restrict (ball x δ)) :=
    ⟨by simpa using hX.finiteOnBounded (ball x δ) isBounded_ball⟩
  have hlip := hX.heatRadonMeasure_set_lipschitz hn p t ht hA
  have hi : IntegrableOn v (ball x δ) μ := by
    apply (integrable_const (1 : ℝ)).mono' hlip.continuous.aestronglyMeasurable.restrict
    exact Eventually.of_forall fun y => by
      change ‖(hX.heatRadonMeasure hn p t ht y).real A‖ ≤ 1
      rw [Real.norm_of_nonneg measureReal_nonneg]
      exact measureReal_le_one
  have hmean : (v x - L*δ) * V ≤ ∫ y in ball x δ, v y ∂μ := by
    have hpoint (y : X) (hy : y ∈ ball x δ) : v x - L*δ ≤ v y := by
      have h := hlip.dist_le_mul x y
      rw [Real.dist_eq] at h
      change |v x-v y| ≤ L * dist x y at h
      have hd : dist x y ≤ δ := by simpa only [dist_comm] using (mem_ball.mp hy).le
      have hm := mul_le_mul_of_nonneg_left hd (Real.sqrt_nonneg (1 / (2*t*Real.exp (-2*|K| * t))))
      have hle := (le_abs_self (v x-v y)).trans h
      change L * dist x y ≤ L * δ at hm
      linarith
    have hh := integral_mono_ae (integrable_const (v x - L*δ)) hi
      ((ae_restrict_mem measurableSet_ball).mono fun y hy => hpoint y hy)
    simpa only [integral_const, smul_eq_mul, V, mul_comm,
      measureReal_restrict_apply MeasurableSet.univ, univ_inter] using hh
  have hu := hX.heatRadonMeasure_separated_sets hn p t ht hA measurableSet_ball hAf
    (hX.finiteOnBounded (ball x δ) isBounded_ball).ne q hnear
    (R := dist q x-δ) (by
      intro y hy
      have htri := dist_triangle q y x
      have hy' := mem_ball.mp hy
      linarith) (by linarith)
  have hprod := hmean.trans hu
  have hsqrt : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV
  let D := Real.exp (-((dist q x-δ)-r)^2 / (4*t)) * Real.sqrt (μ.real A)
  have he : (D / Real.sqrt V) * V = D * Real.sqrt V := by
    rw [div_mul_eq_mul_div, div_eq_iff hsqrt.ne']
    calc
      D * V = D * (Real.sqrt V)^2 := by rw [Real.sq_sqrt hV.le]
      _ = _ := by ring
  have hle : v x - L*δ ≤ D / Real.sqrt V := by
    apply le_of_mul_le_mul_right (a := V)
    · rw [he]
      exact hprod
    · exact hV
  change v x ≤ L*δ + D / Real.sqrt V
  linarith

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
