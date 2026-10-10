import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
namespace SKGapCutoff.RandomMatrix

lemma separated_card_le {n : ℕ} (s : Finset (EuclideanSpace ℝ (Fin n)))
    (hb : ∀ x ∈ s, ‖x‖ ≤ 1)
    (hs : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (1/4:ℝ) < dist x y) :
    (s.card : ℝ) ≤ (9:ℝ)^n := by
  have hd : Set.PairwiseDisjoint (↑s) (fun x : EuclideanSpace ℝ (Fin n) => ball x (1/8)) := by
    intro x hx y hy hxy
    exact ball_disjoint_ball (by linarith [hs x hx y hy hxy])
  have hsub : (⋃ x ∈ s, ball x (1/8)) ⊆ ball (0 : EuclideanSpace ℝ (Fin n)) (9/8) := by
    intro y hy
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.mp hy
    have h := dist_triangle y x (0 : EuclideanSpace ℝ (Fin n))
    simp only [mem_ball, dist_zero_right] at hy h ⊢
    linarith [hb x hx]
  have hm := measureReal_mono (μ := volume) hsub measure_ball_ne_top
  rw [measureReal_biUnion_finset hd (fun _ _ => measurableSet_ball)] at hm
  have hvol (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r) :
      volume.real (ball x r) = r ^ n * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    simp only [measureReal_def, Measure.addHaar_ball_of_pos volume x hr,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le _), finrank_euclideanSpace,
      Fintype.card_fin]
  simp only [hvol _ _ (by norm_num : (0:ℝ) < 1/8),
    hvol _ _ (by norm_num : (0:ℝ) < 9/8), Finset.sum_const, nsmul_eq_mul] at hm
  have hp : 0 < volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    exact ENNReal.toReal_pos (measure_ball_pos volume _ zero_lt_one).ne' measure_ball_ne_top
  have hh : (s.card : ℝ) * (1/8:ℝ)^n ≤ (9/8:ℝ)^n :=
    (mul_le_mul_iff_left₀ hp).mp (by simpa only [mul_assoc] using hm)
  have he : (9/8:ℝ)^n = (9:ℝ)^n * (1/8:ℝ)^n := by rw [← mul_pow]; congr 1; norm_num
  rw [he] at hh
  exact (mul_le_mul_iff_left₀ (show 0 < (1/8:ℝ)^n by positivity)).mp
    (by simpa only [mul_comm] using hh)

lemma unit_ball_net (n : ℕ) :
    ∃ s : Finset (EuclideanSpace ℝ (Fin n)),
      (∀ x ∈ s, ‖x‖ ≤ 1) ∧
      (∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 → ∃ y ∈ s, dist x y ≤ 1/4) ∧
      (s.card : ℝ) ≤ (9:ℝ)^n := by
  classical
  let A := closedBall (0 : EuclideanSpace ℝ (Fin n)) 1
  obtain ⟨C, _, hCf, hC⟩ := exists_finite_isCover_of_isCompact
    (by norm_num : (1/8 : ℝ≥0) ≠ 0) (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
  have hpack : packingNumber (1/4 : ℝ≥0) A ≠ ⊤ := by
    have hle := (packingNumber_two_mul_le_externalCoveringNumber (1/8 : ℝ≥0) A).trans
      hC.externalCoveringNumber_le_encard
    norm_num only [show (2:ℝ≥0)*(1/8) = 1/4 by norm_num] at hle
    exact ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hCf) hle

  let D := maximalSeparatedSet (1/4 : ℝ≥0) A
  have hDf : D.Finite := Set.encard_ne_top_iff.mp (by
    rw [show D = maximalSeparatedSet (1/4 : ℝ≥0) A from rfl, encard_maximalSeparatedSet hpack]
    exact hpack)
  refine ⟨hDf.toFinset, ?_, ?_, ?_⟩
  · intro x hx
    have h := maximalSeparatedSet_subset (ε := (1/4 : ℝ≥0)) (A := A) (hDf.mem_toFinset.mp hx)
    simpa only [A, mem_closedBall, dist_zero_right] using h
  · intro x hx
    have hxA : x ∈ A := by simpa only [A, mem_closedBall, dist_zero_right] using hx
    obtain ⟨y, hy, hdist⟩ := isCover_maximalSeparatedSet hpack hxA
    refine ⟨y, hDf.mem_toFinset.mpr hy, ?_⟩
    change edist x y ≤ ((1/4 : ℝ≥0) : ℝ≥0∞) at hdist
    have h := ENNReal.toReal_mono (by norm_num : ((1/4 : ℝ≥0) : ℝ≥0∞) ≠ ⊤) hdist
    simpa only [edist_dist, ENNReal.toReal_ofReal (dist_nonneg : 0 ≤ dist x y),
      ENNReal.coe_toReal, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using h
  · apply separated_card_le
    · intro x hx
      have h := maximalSeparatedSet_subset (ε := (1/4 : ℝ≥0)) (A := A) (hDf.mem_toFinset.mp hx)
      simpa only [A, mem_closedBall, dist_zero_right] using h
    · intro x hx y hy hxy
      have h := isSeparated_maximalSeparatedSet (ε := (1/4 : ℝ≥0)) (A := A)
        (hDf.mem_toFinset.mp hx) (hDf.mem_toFinset.mp hy) hxy
      simpa only [edist_dist, ENNReal.coe_lt_ofReal, NNReal.coe_div, NNReal.coe_one,
        NNReal.coe_ofNat] using h

lemma opNorm_le_of_net {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (s : Finset (EuclideanSpace ℝ (Fin n)))
    (hb : ∀ x ∈ s, ‖x‖ ≤ 1)
    (hcover : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 → ∃ y ∈ s, dist x y ≤ 1/4)
    (M : ℝ) (hM : 0 ≤ M)
    (hnet : ∀ x ∈ s, ∀ y ∈ s, |inner (𝕜 := ℝ) (A x) y| ≤ M) : ‖A‖ ≤ 2*M := by
  have hh : ‖A‖ ≤ M + ‖A‖/2 := by
    apply ContinuousLinearMap.opNorm_le_of_re_inner_le (by positivity)
    intro x y hx hy
    obtain ⟨a, ha, hxa⟩ := hcover x hx.le
    obtain ⟨b, hb', hyb⟩ := hcover y hy.le
    have hxan : ‖x-a‖ ≤ 1/4 := by simpa only [dist_eq_norm] using hxa
    have hybn : ‖y-b‖ ≤ 1/4 := by simpa only [dist_eq_norm] using hyb
    have h₁ : |inner (𝕜 := ℝ) (A (x-a)) y| ≤ ‖A‖/4 := by
      calc
        _ ≤ ‖A (x-a)‖ * ‖y‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖A‖ * ‖x-a‖) * ‖y‖ := mul_le_mul_of_nonneg_right (A.le_opNorm _) (norm_nonneg _)
        _ ≤ ‖A‖/4 := by rw [hy, mul_one]; nlinarith [norm_nonneg A]
    have h₂ : |inner (𝕜 := ℝ) (A a) (y-b)| ≤ ‖A‖/4 := by
      calc
        _ ≤ ‖A a‖ * ‖y-b‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖A‖ * ‖a‖) * ‖y-b‖ := mul_le_mul_of_nonneg_right (A.le_opNorm _) (norm_nonneg _)
        _ ≤ ‖A‖ * (1:ℝ) * (1/4) := mul_le_mul
          (mul_le_mul_of_nonneg_left (hb a ha) (norm_nonneg A)) hybn (norm_nonneg _) (by positivity)
        _ = ‖A‖/4 := by ring
    have he : inner (𝕜 := ℝ) (A x) y = inner (𝕜 := ℝ) (A (x-a)) y +
        inner (𝕜 := ℝ) (A a) (y-b) + inner (𝕜 := ℝ) (A a) b := by
      simp only [map_sub, inner_sub_left, inner_sub_right]; ring
    change inner (𝕜 := ℝ) (A x) y ≤ M + ‖A‖/2
    rw [he]
    have hh := hnet a ha b hb'
    linarith [le_abs_self (inner (𝕜 := ℝ) (A (x-a)) y),
      le_abs_self (inner (𝕜 := ℝ) (A a) (y-b)), le_abs_self (inner (𝕜 := ℝ) (A a) b)]
  linarith

end SKGapCutoff.RandomMatrix

open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set

end

end OAI
