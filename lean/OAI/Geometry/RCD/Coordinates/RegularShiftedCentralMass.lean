import OAI.Geometry.RCD.Coordinates.RegularRawMassSmallness
import OAI.Geometry.RCD.Heat.UniformHeatBase

namespace OAI

/-! # Central cumulative comparison at the interior heat scale -/

open Set Metric MeasureTheory
open scoped InnerProductSpace BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

namespace RegularBilinearData

variable {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X} [(hausdorff n X).Regular]
  {base : X} {ker : ℝ → X → X → ℝ}
  {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker} {enlargement zeta : ℝ}
  (d : RegularBilinearData hX base hk enlargement zeta)

/-- Discarding seventeen initial terms changes only a uniform finite
constant. Both inequalities concern the actual heat inverse and central
Bochner masses at the same interior scales. -/
theorem shifted_central_mass_comparison :
    ∃ T : ℝ, 0 < T ∧ ∀ q, q ∈ ball base (d.radius / 32) → ∀ (xi : Euclidean n) (k : ℕ),
      let Q := fun i => d.heatAt q (d.shift + i + 17)
      let mass := ∑ i ∈ Finset.range k,
        ⟪(Q i).symm xi, dyadicBochnerMass d.mass n q d.radius (d.shift + i + 17) ((Q i).symm xi)⟫_ℝ
      (‖xi‖ ^ 2 + mass ≤ d.lowerConstant * ‖d.frozenAt q k xi‖ ^ 2) ∧
      (‖d.frozenAt q k xi‖ ^ 2 ≤ T * (‖xi‖ ^ 2 + mass)) := by
  obtain ⟨T₀, hT₀, hbase⟩ := exists_uniform_dyadic_heat_base
    (hausdorff n X) hX.quadratic hk d.energy d.cutoff
    (by linarith [d.radius_pos]) d.radius_pos d.lambda_pos (d.shift + 17)
  let T := d.upperConstant * (1 + d.lowerConstant * T₀)
  have hT : 0 < T := mul_pos d.upperConstant_pos
    (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg d.lowerConstant_pos.le hT₀.le))
  refine ⟨T, hT, ?_⟩
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
        nlinarith only [mul_nonneg d.upperConstant_pos.le h]

end RegularBilinearData
end RegularPointCoordinates

end

end OAI
