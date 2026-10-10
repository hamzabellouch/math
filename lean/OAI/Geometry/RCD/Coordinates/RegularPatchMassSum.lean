import OAI.Geometry.RCD.Coordinates.RegularPatchMassEnvelope

namespace OAI

/-! # Finite patch mass sums and the reverse central-ball covering -/

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

/-- The heat-envelope total controls the full raw mass of every finite
family of sufficiently nearby patches at the moving inverse vectors. -/
theorem raw_patch_mass_sum_le {q : X} (hq : q ∈ ball base (d.radius / 32))
    {ι : Type*} (s : ℕ → Finset ι)
    (centers : ℕ → ι → X) (N : ℕ) (hcard : ∀ i, (s i).card ≤ N)
    (hroom : ∀ i y, y ∈ s i → dist (centers i y) q ≤
      (d.radius / (2 : ℝ) ^ (d.shift + i + 15)) / 12)
    (xi : Euclidean n) (k : ℕ) :
    let Q := fun i => d.heatAt q (d.shift + i + 17)
    (∑ i ∈ Finset.range k, ∑ y ∈ s i,
      ⟪(Q i).symm xi, rawPinchingMass d.mass n d.radius (centers i y) (d.shift + i)
        ((Q i).symm xi)⟫_ℝ) ≤
      (N : ℝ) * patchEnvelopeFactor n * d.envelopeConstant * ‖d.frozenAt q k xi‖ ^ 2 := by
  classical
  intro Q
  let b := fun j => ⟪(d.heatAt q (d.shift + j)).symm xi,
    dyadicBochnerEnvelope d.mass n q d.radius (d.shift + j) ((d.heatAt q (d.shift + j)).symm xi)⟫_ℝ
  have hb (j) : 0 ≤ b j :=
    (dyadicBochnerEnvelope_isPositive d.mass n q d.radius_pos.le _).inner_nonneg_right _
  have hfactor : 0 ≤ patchEnvelopeFactor n := by unfold patchEnvelopeFactor; positivity
  have hpoint i y (hy : y ∈ s i) :
      ⟪(Q i).symm xi, rawPinchingMass d.mass n d.radius (centers i y) (d.shift + i)
        ((Q i).symm xi)⟫_ℝ ≤ patchEnvelopeFactor n * b (i + 17) := by
    have h := rawPinchingMass_le_envelope d.mass n d.radius_pos (d.shift + i)
      (hroom i y hy) ((Q i).symm xi)
    simpa only [b, Q, Nat.add_assoc] using h
  have htotal : (∑ i ∈ Finset.range k, b (i + 17)) ≤
      d.envelopeConstant * ‖d.frozenAt q k xi‖ ^ 2 := by
    have h := ((d.localData q hq).1 xi (k + 17)).1
    change (∑ j ∈ Finset.range (k + 17), b j) ≤
      d.envelopeConstant * ⟪xi, (d.heatAt q (d.shift + (k + 17))).symm xi⟫_ℝ at h
    have hshift := nonnegative_shifted_sum_le b hb 17 k
    rw [show 17 + k = k + 17 by omega] at hshift
    have ht := hshift.trans h
    rw [d.frozenAt_norm_sq]
    simpa only [Nat.add_comm 17, Nat.add_assoc] using ht
  calc
    _ ≤ ∑ i ∈ Finset.range k, (N : ℝ) * (patchEnvelopeFactor n * b (i + 17)) := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ∑ _y ∈ s i, patchEnvelopeFactor n * b (i + 17) := Finset.sum_le_sum (fun y hy => hpoint i y hy)
        _ = ((s i).card : ℝ) * (patchEnvelopeFactor n * b (i + 17)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard i) (mul_nonneg hfactor (hb _))
    _ = ((N : ℝ) * patchEnvelopeFactor n) * ∑ i ∈ Finset.range k, b (i + 17) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ ≤ ((N : ℝ) * patchEnvelopeFactor n) * (d.envelopeConstant * ‖d.frozenAt q k xi‖ ^ 2) :=
      mul_le_mul_of_nonneg_left htotal (mul_nonneg (Nat.cast_nonneg N) hfactor)
    _ = _ := by ring

end RegularBilinearData

/-- The precise scale factor for the strictly interior central mass. -/
def patchCentralFactor (n : ℕ) : ℝ := (65536 : ℝ) ^ 2 / (65536 : ℝ) ^ n

omit [ProperSpace X] in
/-- A center within one twelfth of the mean radius has a mass ball that
covers the central ball two scales below the mean radius. -/
theorem rawPinchingMass_covers_central {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (M : PositiveBilinearMeasure X E) (n : ℕ) {R : ℝ} (hR : 0 < R)
    {q z : X} (i : ℕ) (hroom : dist z q ≤ (R / (2 : ℝ) ^ (i + 15)) / 12) (v : E) :
    patchCentralFactor n * ⟪v, dyadicBochnerMass M n q R (i + 17) v⟫_ℝ ≤
      ⟪v, rawPinchingMass M n R z i v⟫_ℝ := by
  let r := R / (2 : ℝ) ^ (i + 17)
  let s := distanceSourceRadius R i
  have hr : 0 < r := div_pos hR (by positivity)
  have hs : s = 65536 * r := by
    dsimp only [s, r, distanceSourceRadius]
    rw [show i + 17 = (i + 1) + 16 by omega, pow_add]
    norm_num
    ring
  have hmean : R / (2 : ℝ) ^ (i + 15) = 4 * r := by
    dsimp only [r]
    rw [show i + 17 = (i + 15) + 2 by omega, pow_add]
    norm_num
    ring
  have hball : ball q r ⊆ ball z (s / 49152) := by
    apply ball_subset_ball'
    rw [dist_comm]
    rw [hmean] at hroom
    rw [hs]
    linarith
  have hm := measureReal_mono (μ := M.measure v) hball (measure_ne_top _ _)
  rw [M.measure_real v _ measurableSet_ball, M.measure_real v _ measurableSet_ball] at hm
  have hscale : s ^ 2 / s ^ n = patchCentralFactor n * (r ^ 2 / r ^ n) := by
    rw [hs, mul_pow, mul_pow]
    dsimp only [patchCentralFactor]
    ring
  change patchCentralFactor n * ⟪v, ((r ^ 2 / r ^ n) • M.massOperator (ball q r)) v⟫_ℝ ≤
    ⟪v, ((s ^ 2 / s ^ n) • M.massOperator (ball z (s / 49152))) v⟫_ℝ
  rw [smul_apply, inner_smul_right, smul_apply, inner_smul_right, hscale]
  have hspos : 0 < s := by rw [hs]; positivity
  have h := mul_le_mul_of_nonneg_left hm (show 0 ≤ s ^ 2 / s ^ n by positivity)
  rw [hscale] at h
  convert h using 1
  ring

end RegularPointCoordinates

end

end OAI
