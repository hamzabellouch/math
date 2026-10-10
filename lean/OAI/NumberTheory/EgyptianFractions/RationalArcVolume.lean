import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set

namespace Problem337.ThreePrimeAnalysis

/-- A closed rational neighborhood of radius `δ / q`. -/
def rationalArc (q a : ℕ) (δ : ℝ) : Set ℝ :=
  Icc ((a : ℝ) / q - δ / q) ((a : ℝ) / q + δ / q)

/-- All rational neighborhoods with positive denominator at most `Q` and
centers in `[0,1]`. Including nonreduced fractions only enlarges the set. -/
def majorArcUnion (Q : ℕ) (δ : ℝ) : Set ℝ :=
  ⋃ q ∈ Finset.Icc 1 Q, ⋃ a ∈ Finset.range (q + 1), rationalArc q a δ

theorem measurableSet_majorArcUnion (Q : ℕ) (δ : ℝ) :
    MeasurableSet (majorArcUnion Q δ) := by
  unfold majorArcUnion rationalArc
  measurability

theorem volume_rationalArc (q a : ℕ) (δ : ℝ) :
    volume (rationalArc q a δ) = ENNReal.ofReal (2 * δ / q) := by
  rw [rationalArc, Real.volume_Icc]
  congr 1
  ring

theorem mem_rationalArc_iff {q a : ℕ} {δ x : ℝ} :
    x ∈ rationalArc q a δ ↔ |x - (a : ℝ) / q| ≤ δ / q := by
  rw [rationalArc, mem_Icc, abs_le]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem mem_majorArcUnion_iff {Q : ℕ} {δ x : ℝ} :
    x ∈ majorArcUnion Q δ ↔ ∃ q : ℕ, 1 ≤ q ∧ q ≤ Q ∧
      ∃ a : ℕ, a ≤ q ∧ |x - (a : ℝ) / q| ≤ δ / q := by
  simp only [majorArcUnion, mem_iUnion, Finset.mem_Icc, Finset.mem_range,
    Nat.lt_succ_iff, mem_rationalArc_iff]
  aesop

/-- For radii below one, an approximating rational to a point in `[0,1]`
automatically has a numerator in `[0,q]`. Thus integer-indexed Dirichlet
neighborhoods are covered by the finite union used in the volume estimate. -/
theorem near_integer_fraction_mem_majorArcUnion
    {Q q : ℕ} {a : ℤ} {δ x : ℝ} (hq : 0 < q) (hqQ : q ≤ Q)
    (hδ : δ < 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hnear : |x - (a : ℝ) / q| ≤ δ / q) :
    x ∈ majorArcUnion Q δ := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hscaled : |x * (q : ℝ) - a| ≤ δ := by
    calc
      _ = |(x - (a : ℝ) / q) * q| := by
        congr 1
        field_simp
      _ = |x - (a : ℝ) / q| * q := by rw [abs_mul, abs_of_pos hqpos]
      _ ≤ (δ / q) * q := mul_le_mul_of_nonneg_right hnear hqpos.le
      _ = δ := div_mul_cancel₀ _ hqpos.ne'
  have hmul0 : 0 ≤ x * (q : ℝ) := mul_nonneg hx0 hqpos.le
  have hmul1 : x * (q : ℝ) ≤ q := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hx1 hqpos.le
  have ha0 : 0 ≤ a := by
    have hreal : (-1 : ℝ) < a := by linarith [(abs_le.mp hscaled).2]
    have hint : (-1 : ℤ) < a := by exact_mod_cast hreal
    omega
  have haq : a ≤ (q : ℤ) := by
    have hreal : (a : ℝ) < (q : ℝ) + 1 := by linarith [(abs_le.mp hscaled).1]
    have hint : a < (q : ℤ) + 1 := by exact_mod_cast hreal
    omega
  have hacast : (a.toNat : ℝ) = a := by
    exact_mod_cast Int.toNat_of_nonneg ha0
  apply mem_majorArcUnion_iff.mpr
  refine ⟨q, hq, hqQ, a.toNat, Int.toNat_le.mpr haq, ?_⟩
  simpa only [hacast] using hnear

/-- Each fixed denominator contributes at most `4δ`, without any coprimality
or disjointness hypothesis. -/
theorem volume_denominator_arcs_le {q : ℕ} (hq : 1 ≤ q)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    volume (⋃ a ∈ Finset.range (q + 1), rationalArc q a δ) ≤
      ENNReal.ofReal (4 * δ) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
  calc
    _ ≤ ∑ a ∈ Finset.range (q + 1), volume (rationalArc q a δ) :=
      measure_biUnion_finset_le _ _
    _ = ENNReal.ofReal (∑ _a ∈ Finset.range (q + 1), 2 * δ / q) := by
      simp only [volume_rationalArc]
      exact (ENNReal.ofReal_sum_of_nonneg (by intros; positivity)).symm
    _ ≤ ENNReal.ofReal (4 * δ) := by
      apply ENNReal.ofReal_le_ofReal
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hqpos).mpr
      nlinarith

/-- Total major-arc volume, valid even when the neighborhoods overlap. -/
theorem volume_majorArcUnion_le (Q : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    volume (majorArcUnion Q δ) ≤ ENNReal.ofReal (4 * (Q : ℝ) * δ) := by
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 Q,
        volume (⋃ a ∈ Finset.range (q + 1), rationalArc q a δ) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _q ∈ Finset.Icc 1 Q, ENNReal.ofReal (4 * δ) := by
      apply Finset.sum_le_sum
      intro q hq
      exact volume_denominator_arcs_le (Finset.mem_Icc.mp hq).1 hδ
    _ = ENNReal.ofReal (4 * (Q : ℝ) * δ) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (by intros; positivity)]
      simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
        nsmul_eq_mul]
      congr 1
      ring

theorem volume_unit_majorArcs_le (Q : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    volume (Icc (0 : ℝ) 1 ∩ majorArcUnion Q δ) ≤
      ENNReal.ofReal (4 * (Q : ℝ) * δ) :=
  (measure_mono inter_subset_right).trans (volume_majorArcUnion_le Q hδ)

/-- Integrating any uniformly bounded error over a subset of the major arcs
costs at most the elementary volume budget. -/
theorem norm_integral_majorArcs_le
    (Q : ℕ) {δ B : ℝ} (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    {E : Set ℝ} (hE : E ⊆ majorArcUnion Q δ) (f : ℝ → ℂ)
    (hf : ∀ x ∈ E, ‖f x‖ ≤ B) :
    ‖∫ x in E, f x‖ ≤ B * (4 * (Q : ℝ) * δ) := by
  have hvol := (measure_mono hE).trans (volume_majorArcUnion_le Q hδ)
  have hfinite : volume E < (⊤ : ℝ≥0∞) := hvol.trans_lt ENNReal.ofReal_lt_top
  have hreal : volume.real E ≤ 4 * (Q : ℝ) * δ := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
    simpa only [measureReal_def,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 4 * (Q : ℝ) * δ)] using h
  exact (norm_setIntegral_le_of_norm_le_const hfinite hf).trans
    (mul_le_mul_of_nonneg_left hreal hB)

/-- A uniform cubic perturbation estimate for the major-arc approximation. -/
theorem norm_cube_sub_cube_le {z w : ℂ} {B ε : ℝ}
    (hB : 0 ≤ B) (hε : 0 ≤ ε) (hz : ‖z‖ ≤ B) (hw : ‖w‖ ≤ B)
    (hzw : ‖z - w‖ ≤ ε) : ‖z ^ 3 - w ^ 3‖ ≤ 3 * B ^ 2 * ε := by
  have hz2 : ‖z‖ ^ 2 ≤ B ^ 2 := by nlinarith [norm_nonneg z]
  have hw2 : ‖w‖ ^ 2 ≤ B ^ 2 := by nlinarith [norm_nonneg w]
  have hprod : ‖z‖ * ‖w‖ ≤ B ^ 2 := by
    simpa only [pow_two] using mul_le_mul hz hw (norm_nonneg w) hB
  have hsum : ‖z ^ 2 + z * w + w ^ 2‖ ≤ 3 * B ^ 2 := by
    calc
      _ ≤ ‖z ^ 2 + z * w‖ + ‖w ^ 2‖ := norm_add_le _ _
      _ ≤ (‖z ^ 2‖ + ‖z * w‖) + ‖w ^ 2‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ = (‖z‖ ^ 2 + ‖z‖ * ‖w‖) + ‖w‖ ^ 2 := by
        simp only [norm_pow, norm_mul]
      _ ≤ 3 * B ^ 2 := by linarith
  calc
    _ = ‖z - w‖ * ‖z ^ 2 + z * w + w ^ 2‖ := by
      rw [← norm_mul]
      congr 1
      ring
    _ ≤ ε * (3 * B ^ 2) := mul_le_mul hzw hsum (norm_nonneg _) hε
    _ = 3 * B ^ 2 * ε := by ring

/-- The major-arc cubic integral error has an explicit volume factor. This
uses only pointwise approximation; it does not assert prime distribution. -/
theorem norm_integral_cubic_majorArc_error_le
    (Q : ℕ) {δ B ε : ℝ} (hδ : 0 ≤ δ) (hB : 0 ≤ B) (hε : 0 ≤ ε)
    {E : Set ℝ} (hE : E ⊆ majorArcUnion Q δ) (f g phase : ℝ → ℂ)
    (hf : ∀ x ∈ E, ‖f x‖ ≤ B) (hg : ∀ x ∈ E, ‖g x‖ ≤ B)
    (herr : ∀ x ∈ E, ‖f x - g x‖ ≤ ε)
    (hphase : ∀ x ∈ E, ‖phase x‖ ≤ 1) :
    ‖∫ x in E, (f x ^ 3 - g x ^ 3) * phase x‖ ≤
      12 * (Q : ℝ) * δ * B ^ 2 * ε := by
  have hbound := norm_integral_majorArcs_le Q hδ
    (show 0 ≤ 3 * B ^ 2 * ε by positivity) hE
    (fun x => (f x ^ 3 - g x ^ 3) * phase x) (by
      intro x hx
      rw [norm_mul]
      have hc := norm_cube_sub_cube_le hB hε (hf x hx) (hg x hx) (herr x hx)
      simpa only [mul_one] using
        mul_le_mul hc (hphase x hx) (norm_nonneg _) (by positivity))
  convert hbound using 1
  ring

end Problem337.ThreePrimeAnalysis

end

end OAI
