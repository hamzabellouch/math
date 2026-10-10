import OAI.Probability.SwitchChain.SliceEquality
import OAI.Probability.SwitchChain.SliceMoments
import OAI.Probability.SwitchChain.SliceCoefficientAlgebra
import OAI.Probability.SwitchChain.SliceBounds

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.SliceImageNorm

variable {α : Type*} [Fintype α] [sectionDecidableEqα : DecidableEq α]

def equalityImage (q : ℕ) (c : α → α → ℝ) (S : Finset α) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, c i j * SliceMoments.centeredEqual Finset.univ q i j S

theorem coord_sum (S : Finset α) :
    (∑ i, SliceMoments.coord i S) = (S.card : ℝ) := by
  simp [SliceMoments.coord]

theorem centeredEquality_coord (q : ℕ) (S : Finset α) (i j : α) :
    SliceEquality.centeredEquality (fun k => SliceMoments.coord k S)
      (SliceMoments.equalMean (Finset.univ : Finset α) q) i j =
      SliceMoments.centeredEqual Finset.univ q i j S := by
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
    simp [SliceEquality.centeredEquality, SliceEquality.equalityIndicator,
      SliceMoments.centeredEqual, SliceMoments.equalIndicator, SliceMoments.coord, hi, hj]

theorem equalityImage_linearPair (q : ℕ) (S : Finset α) (hS : S.card = q)
    (u : α → ℝ) (hu : ∑ i, u i = 0) :
    equalityImage q (SliceCoefficients.linearPair u) S =
      (2 * (q : ℝ) - (Fintype.card α : ℝ)) * ∑ i, u i * SliceMoments.coord i S := by
  have hb (i : α) : SliceMoments.coord i S = 0 ∨ SliceMoments.coord i S = 1 := by
    by_cases hi : i ∈ S <;> simp [SliceMoments.coord, hi]
  have hs : (∑ i, SliceMoments.coord i S) = (q : ℝ) := by rw [coord_sum, hS]
  have h := SliceEquality.additive_centeredEquality_image
    (fun i => SliceMoments.coord i S) hb q (SliceMoments.equalMean (Finset.univ : Finset α) q) hs u hu
  have ht (i j : α) :
      (u i + u j) * SliceEquality.offDiagonal
        (SliceEquality.centeredEquality (fun k => SliceMoments.coord k S)
          (SliceMoments.equalMean (Finset.univ : Finset α) q)) i j =
      SliceCoefficients.linearPair u i j * SliceMoments.centeredEqual Finset.univ q i j S := by
    by_cases hij : i = j
    · subst j
      simp [SliceEquality.offDiagonal, SliceCoefficients.linearPair]
    · simp [SliceEquality.offDiagonal, SliceCoefficients.linearPair, hij, centeredEquality_coord]
  simpa only [ht, equalityImage] using h

theorem average_equalityImage_linearPair_sq
    (hN : 2 ≤ Fintype.card α) (q : ℕ) (hq : q ≤ Fintype.card α)
    (u : α → ℝ) (hu : ∑ i, u i = 0) :
    SliceMoments.average Finset.univ q
      (fun S => (equalityImage q (SliceCoefficients.linearPair u) S)^2) =
      (2 * (q : ℝ) - (Fintype.card α : ℝ))^2 *
        ((q : ℝ) * ((Fintype.card α : ℝ) - q) /
          ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1))) * (∑ i, (u i)^2) := by
  calc
    _ = SliceMoments.average Finset.univ q (fun S =>
        (2 * (q : ℝ) - (Fintype.card α : ℝ))^2 *
          (∑ i, u i * SliceMoments.coord i S)^2) := by
      apply SliceMoments.average_congr
      intro S hS
      rw [equalityImage_linearPair q S (Finset.mem_powersetCard.mp hS).2 u hu]
      ring
    _ = _ := by
      rw [SliceMoments.average_mul_left]
      have hm := SliceMoments.average_linear_sq_zero_sum
        (Finset.univ : Finset α) q (by simpa using hN) (by simpa using hq) u (by simpa using hu)
      simp only [Finset.card_univ] at hm
      rw [hm]
      ring

include sectionDecidableEqα in
theorem equalMean_complement (hN : 2 ≤ Fintype.card α) (q : ℕ) :
    1 - SliceMoments.equalMean (Finset.univ : Finset α) q =
      2 * (q : ℝ) * ((Fintype.card α : ℝ) - q) /
        ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1)) := by
  have retainedsectionDecidableEqα := sectionDecidableEqα
  have hc : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hN
  have h0 : (Fintype.card α : ℝ) ≠ 0 := by linarith
  have h1 : (Fintype.card α : ℝ) - 1 ≠ 0 := by linarith
  unfold SliceMoments.equalMean
  simp only [Finset.card_univ]
  field_simp
  ring

def linearGramScalar (q : ℕ) : ℝ :=
  (2 * (q : ℝ) - (Fintype.card α : ℝ))^2 /
    (2 * ((Fintype.card α : ℝ) - 2) *
      SliceMoments.equalMean (Finset.univ : Finset α) q)

theorem average_equalityImage_linearPair_sq_ratio
    (hN : 3 ≤ Fintype.card α) (q : ℕ) (hq : q ≤ Fintype.card α)
    (hp : SliceMoments.equalMean (Finset.univ : Finset α) q ≠ 0)
    (u : α → ℝ) (hu : ∑ i, u i = 0) :
    SliceMoments.average Finset.univ q
      (fun S => (equalityImage q (SliceCoefficients.linearPair u) S)^2) =
      linearGramScalar (α := α) q *
        (SliceMoments.equalMean (Finset.univ : Finset α) q *
          (1 - SliceMoments.equalMean (Finset.univ : Finset α) q)) *
        ((∑ i, ∑ j, (SliceCoefficients.linearPair u i j)^2) / 2) := by
  have hc : (3 : ℝ) ≤ Fintype.card α := by exact_mod_cast hN
  have h0 : (Fintype.card α : ℝ) ≠ 0 := by linarith
  have h1 : (Fintype.card α : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (Fintype.card α : ℝ) - 2 ≠ 0 := by linarith
  have hN' : 2 ≤ Fintype.card α := by omega
  rw [average_equalityImage_linearPair_sq hN' q hq u hu,
    SliceCoefficients.linearPair_norm_sq u hu, equalMean_complement hN' q]
  unfold linearGramScalar
  field_simp

theorem average_normalized_linearPair_sq
    (hN : 3 ≤ Fintype.card α) (q : ℕ) (hq : q ≤ Fintype.card α)
    (hp : 0 < SliceMoments.equalMean (Finset.univ : Finset α) q)
    (hp1 : SliceMoments.equalMean (Finset.univ : Finset α) q < 1)
    (u : α → ℝ) (hu : ∑ i, u i = 0) :
    SliceMoments.average Finset.univ q
      (fun S => (equalityImage q (SliceCoefficients.linearPair u) S /
        Real.sqrt (SliceMoments.equalMean (Finset.univ : Finset α) q *
          (1 - SliceMoments.equalMean (Finset.univ : Finset α) q)))^2) =
      linearGramScalar (α := α) q *
        ((∑ i, ∑ j, (SliceCoefficients.linearPair u i j)^2) / 2) := by
  let v : ℝ := SliceMoments.equalMean (Finset.univ : Finset α) q *
    (1 - SliceMoments.equalMean (Finset.univ : Finset α) q)
  have hv : 0 < v := mul_pos hp (sub_pos.mpr hp1)
  have hs : (Real.sqrt v)^2 = v := Real.sq_sqrt hv.le
  change SliceMoments.average Finset.univ q
    (fun S => (equalityImage q (SliceCoefficients.linearPair u) S / Real.sqrt v)^2) = _
  calc
    _ = SliceMoments.average Finset.univ q
        (fun S => (equalityImage q (SliceCoefficients.linearPair u) S)^2) / v := by
      unfold SliceMoments.average
      simp_rw [div_pow, hs]
      rw [← Finset.sum_div]
      ring
    _ = _ := by
      rw [average_equalityImage_linearPair_sq_ratio hN q hq hp.ne' u hu]
      change (linearGramScalar (α := α) q * v *
        ((∑ i, ∑ j, (SliceCoefficients.linearPair u i j)^2) / 2)) / v = _
      field_simp

include sectionDecidableEqα in
theorem equalMean_pos (hN : 3 ≤ Fintype.card α) (q : ℕ) :
    0 < SliceMoments.equalMean (Finset.univ : Finset α) q := by
  have retainedsectionDecidableEqα := sectionDecidableEqα
  have hN3 : (3 : ℝ) ≤ Fintype.card α := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < Fintype.card α := by linarith
  have hN1 : (0 : ℝ) < (Fintype.card α : ℝ) - 1 := by linarith
  have hN2 : (0 : ℝ) < (Fintype.card α : ℝ) - 2 := by linarith
  have hnprod := mul_pos hN0 hN2
  unfold SliceMoments.equalMean
  simp only [Finset.card_univ]
  apply div_pos _ (mul_pos hN0 hN1)
  nlinarith [sq_nonneg ((q : ℝ) - ((Fintype.card α : ℝ) - q))]

theorem equalMean_lt_one (hN : 2 ≤ Fintype.card α) (q : ℕ)
    (hq0 : 0 < q) (hqN : q < Fintype.card α) :
    SliceMoments.equalMean (Finset.univ : Finset α) q < 1 := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq0
  have hqcard : (q : ℝ) < Fintype.card α := by exact_mod_cast hqN
  have hN2 : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hN
  have hdiff : 0 < 1 - SliceMoments.equalMean (Finset.univ : Finset α) q := by
    rw [equalMean_complement hN q]
    apply div_pos
    · exact mul_pos (mul_pos (by norm_num) hqpos) (sub_pos.mpr hqcard)
    · exact mul_pos (by linarith) (by linarith)
  linarith

theorem average_normalized_linearPair_sq_of_nontrivial
    (hN : 3 ≤ Fintype.card α) (q : ℕ)
    (hq0 : 0 < q) (hqN : q < Fintype.card α)
    (u : α → ℝ) (hu : ∑ i, u i = 0) :
    SliceMoments.average Finset.univ q
      (fun S => (equalityImage q (SliceCoefficients.linearPair u) S /
        Real.sqrt (SliceMoments.equalMean (Finset.univ : Finset α) q *
          (1 - SliceMoments.equalMean (Finset.univ : Finset α) q)))^2) =
      linearGramScalar (α := α) q *
        ((∑ i, ∑ j, (SliceCoefficients.linearPair u i j)^2) / 2) := by
  apply average_normalized_linearPair_sq hN q hqN.le
    (equalMean_pos hN q) (equalMean_lt_one (by omega) q hq0 hqN) u hu

include sectionDecidableEqα in
theorem linearGramScalar_le
    (hN : 3 ≤ Fintype.card α) (q : ℕ)
    (hq0 : 0 < q) (hqN : q < Fintype.card α) :
    linearGramScalar (α := α) q ≤ (Fintype.card α : ℝ) / 2 := by
  have retainedsectionDecidableEqα := sectionDecidableEqα
  have hNc : (3 : ℝ) ≤ Fintype.card α := by exact_mod_cast hN
  have hqc : (1 : ℝ) ≤ q := by exact_mod_cast hq0
  have hqnext : q + 1 ≤ Fintype.card α := by omega
  have hqnextc : (q : ℝ) + 1 ≤ Fintype.card α := by exact_mod_cast hqnext
  have hr : (1 : ℝ) ≤ (Fintype.card α : ℝ) - q := by linarith
  have h := SliceBounds.linear_eigenvalue_le hNc hqc hr
    (by ring : (q : ℝ) + ((Fintype.card α : ℝ) - q) = Fintype.card α)
  simpa only [linearGramScalar, SliceBounds.equalityProbability, SliceMoments.equalMean,
    Finset.card_univ] using h

theorem average_normalized_linearPair_sq_le
    (hN : 3 ≤ Fintype.card α) (q : ℕ)
    (hq0 : 0 < q) (hqN : q < Fintype.card α)
    (u : α → ℝ) (hu : ∑ i, u i = 0) :
    SliceMoments.average Finset.univ q
      (fun S => (equalityImage q (SliceCoefficients.linearPair u) S /
        Real.sqrt (SliceMoments.equalMean (Finset.univ : Finset α) q *
          (1 - SliceMoments.equalMean (Finset.univ : Finset α) q)))^2) ≤
      ((Fintype.card α : ℝ) / 2) *
        ((∑ i, ∑ j, (SliceCoefficients.linearPair u i j)^2) / 2) := by
  rw [average_normalized_linearPair_sq_of_nontrivial hN q hq0 hqN u hu]
  apply mul_le_mul_of_nonneg_right (linearGramScalar_le hN q hq0 hqN)
  positivity

end Problem315.SliceImageNorm

end

end OAI
