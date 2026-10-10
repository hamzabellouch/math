import OAI.Geometry.RCD.Coordinates.RegularShiftedNormalization

namespace OAI

/-! # Summing actual normalization errors at the interior heat scale -/

open Set Metric MeasureTheory
open scoped InnerProductSpace BigOperators

noncomputable section
namespace RegularPointCoordinates

/-- A nonnegative shifted block is bounded by its full initial segment. -/
theorem nonnegative_shifted_sum_le (b : ℕ → ℝ) (hb : ∀ i, 0 ≤ b i) (l k : ℕ) :
    (∑ i ∈ Finset.range k, b (l + i)) ≤ ∑ i ∈ Finset.range (l + k), b i := by
  induction k with
  | zero => simpa using Finset.sum_nonneg (fun i (_ : i ∈ Finset.range l) => hb i)
  | succ k ih =>
      rw [Finset.sum_range_succ, Nat.add_succ, Finset.sum_range_succ]
      linarith only [ih]

/-- Two-scale nonnegative increments telescope with multiplicity two. -/
theorem two_step_energy_sum_le (H : ℕ → ℝ) (hH : ∀ i, 0 ≤ H i)
    (hmono : Monotone H) (k : ℕ) :
    (∑ i ∈ Finset.range k, (H (i + 2) - H i)) ≤ 2 * H (k + 2) := by
  have heq : (∑ i ∈ Finset.range k, (H (i + 2) - H i)) =
      (H (k + 1) - H 1) + (H k - H 0) := by
    calc
      _ = (∑ i ∈ Finset.range k, (H (i + 1 + 1) - H (i + 1))) +
          (∑ i ∈ Finset.range k, (H (i + 1) - H i)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [show i + 1 + 1 = i + 2 by omega]
        ring
      _ = _ := by
        have h := Finset.sum_range_sub (fun i => H (i + 1)) k
        rw [h, Finset.sum_range_sub]
  rw [heq]
  linarith [hH 0, hH 1, hmono (show k + 1 ≤ k + 2 by omega), hmono (show k ≤ k + 2 by omega)]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The actual mean-to-interior-heat errors have one cumulative bound for
any finite choice of nearby centers, with only its multiplicity as a loss. -/
theorem regular_shifted_inverse_errors_sum_le {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base : X} {a κ B J C A Cχ enlargement zeta eta : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    {q : X} (hq : q ∈ ball base (e.heat.radius / 32)) (hzeta : 0 ≤ zeta)
    (hsmall : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 2 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 4)
    {ι : Type*} (s : ℕ → Finset ι)
    (centers : ℕ → ι → {z : X // z ∈ ball base (e.heat.radius / 32)})
    (N : ℕ) (hcard : ∀ i, (s i).card ≤ N)
    (hroom : ∀ i y, y ∈ s i → dist (centers i y).val q ≤
      e.heat.radius / (2 : ℝ) ^ (e.heat.shift + i + 15))
    (henlargement : ∀ i y, y ∈ s i → dist q (centers i y).val ≤
      enlargement * (e.heat.radius / (2 : ℝ) ^ (e.heat.shift + i + 15)))
    (xi : Euclidean n) (k : ℕ) :
    let Q := fun i => e.heat.heatAt q (e.heat.shift + i + 17)
    let R := fun i y => e.heat.meanAt (centers i y).val (centers i y).property
      (e.heat.shift + i + 15)
    (∑ i ∈ Finset.range k, ∑ y ∈ s i,
      ⟪(R i y).symm xi - (Q i).symm xi,
        Q i ((R i y).symm xi - (Q i).symm xi)⟫_ℝ) ≤
      (N : ℝ) * (32 * e.heat.comparisonConstant * e.heat.envelopeConstant + 4) *
        ⟪xi, (Q k).symm xi⟫_ℝ := by
  classical
  intro Q R
  let H := fun i => ⟪xi, (e.heat.heatAt q (e.heat.shift + i + 15)).symm xi⟫_ℝ
  let b := fun i => ⟪(e.heat.heatAt q (e.heat.shift + i)).symm xi,
    dyadicBochnerEnvelope e.heat.mass n q e.heat.radius (e.heat.shift + i)
      ((e.heat.heatAt q (e.heat.shift + i)).symm xi)⟫_ℝ
  have hH (i) : 0 ≤ H i :=
    (positive_equiv_symm _ (e.heat.heatAt_isPositive q _)).inner_nonneg_right _
  have hb (i) : 0 ≤ b i :=
    (dyadicBochnerEnvelope_isPositive e.heat.mass n q e.heat.radius_pos.le _).inner_nonneg_right _
  have hmono : Monotone H := by
    apply monotone_nat_of_le_succ
    intro i
    have h := (inverse_increment_isPositive _ _
      (e.heat.heatAt_isPositive q (e.heat.shift + i + 15))
      (e.heat.heatAt_isPositive q (e.heat.shift + i + 15 + 1))
      (e.heat.heatAt_decrement_positive hq _ (by omega))).inner_nonneg_right xi
    simp only [sub_apply, inner_sub_right, ContinuousLinearEquiv.coe_coe] at h
    change H i ≤ H (i + 1)
    dsimp only [H]
    rw [show e.heat.shift + (i + 1) + 15 = e.heat.shift + i + 15 + 1 by omega]
    linarith only [h]
  have hblock : (∑ i ∈ Finset.range k, b (i + 15)) ≤
      e.heat.envelopeConstant * H (k + 2) := by
    have hshift := nonnegative_shifted_sum_le b hb 15 k
    have hprefix : (∑ i ∈ Finset.range (15 + k), b i) ≤
        ∑ i ∈ Finset.range (k + 17), b i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun i _ _ => hb i)
    have h := ((e.heat.localData q hq).1 xi (k + 17)).1
    change (∑ i ∈ Finset.range (k + 17), b i) ≤ _ at h
    change (∑ i ∈ Finset.range (k + 17), b i) ≤ e.heat.envelopeConstant *
      ⟪xi, (e.heat.heatAt q (e.heat.shift + (k + 17))).symm xi⟫_ℝ at h
    rw [← show e.heat.shift + (k + 2) + 15 = e.heat.shift + (k + 17) by omega] at h
    change (∑ i ∈ Finset.range (k + 17), b i) ≤ e.heat.envelopeConstant * H (k + 2) at h
    have ht := (hshift.trans hprefix).trans h
    simpa only [Nat.add_comm 15] using ht
  have hinc := two_step_energy_sum_le H hH hmono k
  let t := fun i => 32 * e.heat.comparisonConstant * b (i + 15) + 2 * (H (i + 2) - H i)
  have ht (i) : 0 ≤ t i := add_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) e.heat.comparisonConstant_pos.le) (hb (i + 15)))
    (mul_nonneg (by norm_num) (sub_nonneg.mpr (hmono (by omega))))
  have hpoint (i y) (hy : y ∈ s i) :
      ⟪(R i y).symm xi - (Q i).symm xi,
        Q i ((R i y).symm xi - (Q i).symm xi)⟫_ℝ ≤ t i := by
    have h := regular_shifted_inverse_error hX e hq (centers i y).property hzeta hsmall
      (e.heat.shift + i) (by omega) (hroom i y hy) (henlargement i y hy) xi
    simpa only [R, Q, t, b, H, Nat.add_assoc, Nat.reduceAdd] using h
  have hs : (∑ i ∈ Finset.range k, ∑ y ∈ s i,
      ⟪(R i y).symm xi - (Q i).symm xi,
        Q i ((R i y).symm xi - (Q i).symm xi)⟫_ℝ) ≤ (N : ℝ) * ∑ i ∈ Finset.range k, t i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc
      _ ≤ ∑ _y ∈ s i, t i := Finset.sum_le_sum (fun y hy => hpoint i y hy)
      _ = ((s i).card : ℝ) * t i := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard i) (ht i)
  have htsum : (∑ i ∈ Finset.range k, t i) ≤
      (32 * e.heat.comparisonConstant * e.heat.envelopeConstant + 4) * H (k + 2) := by
    simp only [t, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h0 := mul_le_mul_of_nonneg_left hblock
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 32) e.heat.comparisonConstant_pos.le)
    have h1 := mul_le_mul_of_nonneg_left hinc (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [h0, h1]
  have h := hs.trans (mul_le_mul_of_nonneg_left htsum (Nat.cast_nonneg N))
  simpa only [Q, H, show e.heat.shift + (k + 2) + 15 = e.heat.shift + k + 17 by omega, mul_assoc] using h

end RegularPointCoordinates

end

end OAI
