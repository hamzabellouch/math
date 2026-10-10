import OAI.Geometry.RCD.Coordinates.ScaledRegularData
import OAI.Geometry.RCD.Coordinates.RegularShiftedCentralMass

namespace OAI

/-! # Fixed central cumulative constants for the scaled construction -/

open Set Metric MeasureTheory
open scoped InnerProductSpace BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The central cumulative constant is fixed before selecting any
neighborhood realizing the construction parameters. -/
theorem exists_scaled_central_mass_comparison {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base : X} {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (c : RegularHeatConstants n) :
    ∃ T : ℝ, 0 < T ∧ ∀ {enlargement zeta : ℝ}
      (d : RegularBilinearData hX base hk enlargement zeta), c.Matches d →
      ∀ q, q ∈ ball base (d.radius / 32) → ∀ (xi : Euclidean n) (k : ℕ),
      let Q := fun i => d.heatAt q (d.shift + i + 17)
      let mass := ∑ i ∈ Finset.range k,
        ⟪(Q i).symm xi, dyadicBochnerMass d.mass n q d.radius (d.shift + i + 17) ((Q i).symm xi)⟫_ℝ
      (‖xi‖ ^ 2 + mass ≤ d.lowerConstant * ‖d.frozenAt q k xi‖ ^ 2) ∧
      (‖d.frozenAt q k xi‖ ^ 2 ≤ T * (‖xi‖ ^ 2 + mass)) := by
  let Lambda := 8 * (n : ℝ) ^ 2 + 2
  have hLambda : 0 < Lambda := by dsimp only [Lambda]; positivity
  obtain ⟨T₀, hT₀, hbaseBuild⟩ := exists_scaled_dyadic_heat_base
    (hausdorff n X) hX.quadratic hk n (c.shift + 17) hLambda
    (show 0 ≤ 4 * (n : ℝ) ^ 2 by positivity)
  let T := c.upper * (1 + c.lower * T₀)
  have hT : 0 < T := mul_pos c.upper_pos
    (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg c.lower_pos.le hT₀.le))
  refine ⟨T, hT, ?_⟩
  intro enlargement zeta d hmatch
  obtain ⟨_, hshift, _, hlower, hupper, _, hlambdaScale, _⟩ := hmatch
  have hlambda : d.lambda = Lambda / d.radius ^ 2 :=
    (eq_div_iff (ne_of_gt (sq_pos_of_pos d.radius_pos))).mpr hlambdaScale
  have hbase := hbaseBuild d.radius d.radius_pos _ d.mass |K| (4 * d.radius)
    (3 * d.radius / 8) d.cutoffConstant base d.energyBound d.energy d.cutoff
    (by linarith only [d.radius_pos]) d.energyBound_sq
  simp only [← hlambda, ← hshift] at hbase
  intro q hq xi k Q mass
  let b := fun i => ⟪(d.heatAt q (d.shift + i)).symm xi,
    dyadicBochnerMass d.mass n q d.radius (d.shift + i) ((d.heatAt q (d.shift + i)).symm xi)⟫_ℝ
  have hb (i) : 0 ≤ b i :=
    (dyadicBochnerMass_isPositive d.mass n q d.radius_pos.le _).inner_nonneg_right _
  have hmass : mass = ∑ i ∈ Finset.range k, b (17 + i) := by
    dsimp only [mass, b, Q]
    apply Finset.sum_congr rfl
    intro i _
    rw [show d.shift + i + 17 = d.shift + (17 + i) by omega]
  have hsplit : (∑ i ∈ Finset.range (k + 17), b i) =
      (∑ i ∈ Finset.range 17, b i) + mass := by
    rw [show k + 17 = 17 + k by omega, Finset.sum_range_add, ← hmass]
  have hprefix : (∑ i ∈ Finset.range 17, b i) ≤ d.lowerConstant * T₀ * ‖xi‖ ^ 2 := by
    have h := ((d.localData q hq).1 xi 17).2.1
    change ‖xi‖ ^ 2 + (∑ i ∈ Finset.range 17, b i) ≤
      d.lowerConstant * ⟪xi, (d.heatAt q (d.shift + 17)).symm xi⟫_ℝ at h
    have hupper := (hbase q xi).1.1
    change ⟪xi, (d.heatAt q (d.shift + 17)).symm xi⟫_ℝ ≤ T₀ * ‖xi‖ ^ 2 at hupper
    have hh := mul_le_mul_of_nonneg_left hupper d.lowerConstant_pos.le
    nlinarith only [h, hh, sq_nonneg ‖xi‖]
  have hlo := ((d.localData q hq).1 xi (k + 17)).2.1
  have hup := ((d.localData q hq).1 xi (k + 17)).2.2
  change ‖xi‖ ^ 2 + (∑ i ∈ Finset.range (k + 17), b i) ≤
    d.lowerConstant * ⟪xi, (d.heatAt q (d.shift + (k + 17))).symm xi⟫_ℝ at hlo
  change ⟪xi, (d.heatAt q (d.shift + (k + 17))).symm xi⟫_ℝ ≤
    d.upperConstant * (‖xi‖ ^ 2 + (∑ i ∈ Finset.range (k + 17), b i)) at hup
  rw [hsplit] at hlo hup
  have hnonneg := Finset.sum_nonneg (fun i (_ : i ∈ Finset.range 17) => hb i)
  have hmass0 : 0 ≤ mass := by rw [hmass]; exact Finset.sum_nonneg (fun i _ => hb (17 + i))
  rw [d.frozenAt_norm_sq]
  rw [show d.shift + k + 17 = d.shift + (k + 17) by omega]
  constructor
  · linarith only [hlo, hnonneg]
  · calc
      _ ≤ d.upperConstant * (‖xi‖ ^ 2 + (∑ i ∈ Finset.range 17, b i) + mass) := by nlinarith only [hup]
      _ ≤ d.upperConstant * (‖xi‖ ^ 2 + d.lowerConstant * T₀ * ‖xi‖ ^ 2 + mass) :=
        mul_le_mul_of_nonneg_left (by linarith only [hprefix]) d.upperConstant_pos.le
      _ ≤ T * (‖xi‖ ^ 2 + mass) := by
        have h := mul_nonneg (mul_nonneg d.lowerConstant_pos.le hT₀.le) hmass0
        dsimp only [T]
        rw [← hupper, ← hlower]
        nlinarith only [mul_nonneg d.upperConstant_pos.le h]

end RegularPointCoordinates

end

end OAI
