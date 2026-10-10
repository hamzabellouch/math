import OAI.InformationTheory.BooleanNoise.CubeSplits
import OAI.InformationTheory.BooleanNoise.JensenGaps
import OAI.InformationTheory.BooleanNoise.PerspectiveJensen
import OAI.InformationTheory.SoftChannel.SemigroupFlow

namespace OAI

section

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

section Weighted

universe u

variable {ι : Type u} [Fintype ι]

abbrev JensenGaps_entropySeriesCoeff (j : ℕ) : ℝ := psiCoeff j

theorem JensenGaps_entropy_series_gap_lower (F : ℝ → ℝ) (w x : ι → ℝ) (y : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1) (hmean : ∑ i, w i * x i = y)
    (hx : ∀ i, HasSum (fun j => JensenGaps_entropySeriesCoeff j * (x i) ^ (2 * (j + 1))) (F (x i)))
    (hy : HasSum (fun j => JensenGaps_entropySeriesCoeff j * y ^ (2 * (j + 1))) (F y)) :
    (∑ i, w i * (x i) ^ 2) - y ^ 2 ≤ 2 * ((∑ i, w i * F (x i)) - F y) := by
  have hsum := weighted_series_gap_hasSum JensenGaps_entropySeriesCoeff (fun j => 2 * (j + 1)) F w x y hx hy
  apply hasSum_le _ (hasSum_ite_eq (0 : ℕ) ((∑ i, w i * (x i) ^ 2) - y ^ 2)) hsum
  intro j
  by_cases hj : j = 0
  · subst j
    norm_num [JensenGaps_entropySeriesCoeff]
  · simp only [ite_eq_right hj]
    have hp := weighted_even_pow_jensen w x (j + 1) hw hprob
    rw [hmean] at hp
    exact mul_nonneg (mul_nonneg (by norm_num) (psiCoeff_nonneg j)) (sub_nonneg.mpr hp)

theorem JensenGaps_entropy_series_gap_strengthened (F : ℝ → ℝ) (w x : ι → ℝ) (y : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1) (hmean : ∑ i, w i * x i = y)
    (hx0 : ∀ i, 0 ≤ x i) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hx : ∀ i, HasSum (fun j => JensenGaps_entropySeriesCoeff j * (x i) ^ (2 * (j + 1))) (F (x i)))
    (hy : HasSum (fun j => JensenGaps_entropySeriesCoeff j * y ^ (2 * (j + 1))) (F y)) :
    ((∑ i, w i * (x i) ^ 2) - y ^ 2) * lambda (y ^ 2) ≤
      2 * ((∑ i, w i * F (x i)) - F y) := by
  have hsum := weighted_series_gap_hasSum JensenGaps_entropySeriesCoeff (fun j => 2 * (j + 1)) F w x y hx hy
  have hlambda := (hasSum_lambda (sq_nonneg y) (by nlinarith : y ^ 2 < 1)).mul_left
    ((∑ i, w i * (x i) ^ 2) - y ^ 2)
  apply hasSum_le _ hlambda hsum
  intro j
  have hp := weighted_pow_gap_lower w x y (2 * j) hw hprob hx0 hy0 hmean
  have hc : 0 ≤ 2 * JensenGaps_entropySeriesCoeff j := mul_nonneg (by norm_num) (psiCoeff_nonneg j)
  have h := mul_le_mul_of_nonneg_left hp hc
  have heq : 2 * JensenGaps_entropySeriesCoeff j *
      ((2 * j + 1 : ℝ) * y ^ (2 * j) * ((∑ i, w i * (x i) ^ 2) - y ^ 2)) =
      ((∑ i, w i * (x i) ^ 2) - y ^ 2) * ((y ^ 2) ^ j / ((j : ℝ) + 1)) := by
    simp only [JensenGaps_entropySeriesCoeff, psiCoeff, pow_mul]
    field_simp
  rw [show 2 * j + 2 = 2 * (j + 1) by omega] at h
  push_cast at h
  rwa [heq] at h

theorem JensenGaps_normalized_ratio_weights_data (w t b : ι → ℝ) (T k : ℝ)
    (hw : ∀ i, 0 ≤ w i) (ht : ∀ i, 0 < t i) (hT : 0 < T)
    (hmass : ∑ i, w i * t i = T) (hmean : ∑ i, w i * b i = k) :
    (∀ i, 0 ≤ w i * t i / T) ∧ (∑ i, w i * t i / T) = 1 ∧
      (∑ i, (w i * t i / T) * (b i / t i)) = k / T := by
  refine ⟨fun i => div_nonneg (mul_nonneg (hw i) (ht i).le) hT.le, ?_, ?_⟩
  · rw [← Finset.sum_div, hmass, div_self hT.ne']
  · calc
      _ = ∑ i, (w i * b i) / T := by
        apply Finset.sum_congr rfl
        intro i _
        field_simp [(ht i).ne']
      _ = k / T := by rw [← Finset.sum_div, hmean]

theorem JensenGaps_rescale_perspective_gap (w t b : ι → ℝ) (T k C : ℝ)
    (ht : ∀ i, 0 < t i) (hT : 0 < T)
    (hgap : ((∑ i, (w i * t i / T) * (b i / t i) ^ 2) - (k / T) ^ 2) * C ≤
      2 * ((∑ i, (w i * t i / T) * psi (b i / t i)) - psi (k / T))) :
    ((∑ i, w i * (b i) ^ 2 / t i) - k ^ 2 / T) * C ≤
      2 * ((∑ i, w i * t i * psi (b i / t i)) - T * psi (k / T)) := by
  have hsecond : (∑ i, (w i * t i / T) * (b i / t i) ^ 2) =
      (∑ i, w i * (b i) ^ 2 / t i) / T := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [(ht i).ne']
  have hentropy : (∑ i, (w i * t i / T) * psi (b i / t i)) =
      (∑ i, w i * t i * psi (b i / t i)) / T := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsecond, hentropy] at hgap
  have h := mul_le_mul_of_nonneg_left hgap hT.le
  convert! h using 1 <;> field_simp

theorem JensenGaps_pair_reciprocal_square_identity (a b : ℝ) (h : |a| + |b| < 1) :
    b ^ 2 / (1 + a) + b ^ 2 / (1 - a) = 2 * (b ^ 2 / (1 - a ^ 2)) := by
  have hp := (pair_denom_add_pos a b h).ne'
  have hm := (pair_denom_sub_pos a b h).ne'
  have hv := (pair_variance_pos a b h).ne'
  field_simp
  ring

theorem JensenGaps_weighted_pair_gap_combine (w a b : ι → ℝ) (m k C : ℝ)
    (hdom : ∀ i, |a i| + |b i| < 1) (hcenter : |m| + |k| < 1)
    (hp : ((∑ i, w i * (b i) ^ 2 / (1 + a i)) - k ^ 2 / (1 + m)) * C ≤
      2 * ((∑ i, w i * (1 + a i) * psi (b i / (1 + a i))) -
        (1 + m) * psi (k / (1 + m))))
    (hm : ((∑ i, w i * (b i) ^ 2 / (1 - a i)) - k ^ 2 / (1 - m)) * C ≤
      2 * ((∑ i, w i * (1 - a i) * psi (b i / (1 - a i))) -
        (1 - m) * psi (k / (1 - m)))) :
    ((∑ i, w i * (b i) ^ 2 / (1 - (a i) ^ 2)) - k ^ 2 / (1 - m ^ 2)) * C ≤
      2 * ((∑ i, w i * pairEntropyGap (a i) (b i)) - pairEntropyGap m k) := by
  have hv : (∑ i, w i * (b i) ^ 2 / (1 + a i)) +
      (∑ i, w i * (b i) ^ 2 / (1 - a i)) =
      2 * (∑ i, w i * (b i) ^ 2 / (1 - (a i) ^ 2)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = w i * ((b i) ^ 2 / (1 + a i) + (b i) ^ 2 / (1 - a i)) := by ring
      _ = _ := by rw [JensenGaps_pair_reciprocal_square_identity (a i) (b i) (hdom i)]; ring
  have hvc := JensenGaps_pair_reciprocal_square_identity m k hcenter
  have he : (∑ i, w i * (1 + a i) * psi (b i / (1 + a i))) +
      (∑ i, w i * (1 - a i) * psi (b i / (1 - a i))) =
      2 * (∑ i, w i * pairEntropyGap (a i) (b i)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [pairEntropyGap_weighted (a i) (b i) (hdom i)]
    ring
  have hec : (1 + m) * psi (k / (1 + m)) + (1 - m) * psi (k / (1 - m)) =
      2 * pairEntropyGap m k := by
    rw [pairEntropyGap_weighted m k hcenter]
    ring
  have hvC := congrArg (fun z : ℝ => z * C) hv
  have hvcC := congrArg (fun z : ℝ => z * C) hvc
  nlinarith only [hp, hm, hvC, hvcC, he, hec]

theorem JensenGaps_lambda_ratio_min_le (m k t : ℝ) (hk : 0 ≤ k)
    (ht : 0 < t) (htmax : t ≤ 1 + |m|) (hkt : k < t) :
    lambda ((k / (1 + |m|)) ^ 2) ≤ lambda ((k / t) ^ 2) := by
  have hmax : 0 < 1 + |m| := by positivity
  have hx : 0 ≤ k / (1 + |m|) := div_nonneg hk hmax.le
  have hy : 0 ≤ k / t := div_nonneg hk ht.le
  have hxy := div_le_div_of_nonneg_left hk ht htmax
  have hy1 : k / t < 1 := (div_lt_one ht).mpr hkt
  apply monotoneOn_lambda
  · exact ⟨sq_nonneg _, by nlinarith⟩
  · exact ⟨sq_nonneg _, by nlinarith⟩
  · exact pow_le_pow_left₀ hx hxy 2

end Weighted

theorem JensenGaps_cube_uniform_weights_sum_one (n : ℕ) :
    ∑ _ : Cube n, ((2 : ℝ) ^ n)⁻¹ = 1 := by
  simp [Cube, LeanBlast.GotsmanLinial.Cube]

theorem JensenGaps_cubeAverage_as_weighted_sum {n : ℕ} (f : Cube n → ℝ) :
    cubeAverage f = ∑ x, ((2 : ℝ) ^ n)⁻¹ * f x := by
  rw [cubeAverage, ← Finset.mul_sum]
  ring

end LeanBlast.CourtadeKumar
end
end

end OAI
