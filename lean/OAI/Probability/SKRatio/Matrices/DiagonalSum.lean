import Mathlib

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Real
noncomputable section
open scoped BigOperators Topology
open Filter Real
namespace SKRatioGaussian
section MatrixScale
variable {ι : Type*} [Fintype ι]

lemma diagonal_sum_le {a : ι → ℝ} {A : ℝ} (hA : ∀ i, a i ≤ A) :
    (∑ i, a i) ≤ (Fintype.card ι : ℝ) * A := by
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
    Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hA i)

lemma diagonal_sq_sum_le {a : ι → ℝ} {A : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) :
    (∑ i, (a i)^2) ≤ (Fintype.card ι : ℝ) * A^2 :=
  diagonal_sum_le (fun i => by nlinarith [ha i, hA i])

lemma scaled_mean_bound [Nonempty ι] {j A : ℝ} {a : ι → ℝ}
    (hj : 0 ≤ j) (hA : ∀ i, a i ≤ A) :
    (j / (Fintype.card ι : ℝ)) * (∑ i, a i) ≤ j*A := by
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := mul_le_mul_of_nonneg_left (diagonal_sum_le hA) (div_nonneg hj hn.le)
  calc
    _ ≤ _ := h
    _ = _ := by field_simp

lemma scaled_variance_bound [Nonempty ι] {j A : ℝ} {a : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) :
    2*(j / (Fintype.card ι : ℝ))^2 * (∑ i, (a i)^2) ≤
      2*j^2*A^2 / (Fintype.card ι : ℝ) := by
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := mul_le_mul_of_nonneg_left (diagonal_sq_sum_le ha hA)
    (show 0 ≤ 2*(j / (Fintype.card ι : ℝ))^2 by positivity)
  calc
    _ ≤ _ := h
    _ = _ := by field_simp

lemma scaled_sqrt_mean_bound [Nonempty ι] {j A : ℝ} {a : ι → ℝ}
    (hj : 0 ≤ j) (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) (hA0 : 0 ≤ A) :
    sqrt ((j / (Fintype.card ι : ℝ)) * (∑ i, a i)) * sqrt A ≤ sqrt j * A := by
  have hn : 0 ≤ (Fintype.card ι : ℝ) := by positivity
  have hq : 0 ≤ (j / (Fintype.card ι : ℝ)) * ∑ i, a i :=
    mul_nonneg (div_nonneg hj hn) (Finset.sum_nonneg (fun i _ => ha i))
  rw [← sqrt_mul hq]
  calc
    _ ≤ sqrt (j * A^2) := sqrt_le_sqrt (by
      have h := mul_le_mul_of_nonneg_right (scaled_mean_bound hj hA) hA0
      nlinarith only [h])
    _ = sqrt j * A := by rw [sqrt_mul hj, sqrt_sq hA0]

lemma subcritical_endpoint_margin {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    b^2 ≤ 1 - (1-b)^2/2 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hb1) (show 0 ≤ 3*b+1 by positivity)]

lemma scaled_qA_bound [Nonempty ι] {j A : ℝ} {a : ι → ℝ}
    (hj : 0 ≤ j) (hA : ∀ i, a i ≤ A) (hA0 : 0 ≤ A)
    (hsub : sqrt j * A ≤ 1) :
    ((j / (Fintype.card ι : ℝ)) * (∑ i, a i))*A ≤
      1-(1-sqrt j*A)^2/2 := by
  have h := mul_le_mul_of_nonneg_right (scaled_mean_bound hj hA) hA0
  have hm := subcritical_endpoint_margin (show 0 ≤ sqrt j*A by positivity) hsub
  have he : (sqrt j*A)^2 = j*A^2 := by rw [mul_pow, sq_sqrt hj]
  rw [he] at hm
  nlinarith only [h, hm]

end MatrixScale

lemma diagonal_error_tendsto (j A : ℝ) :
    Tendsto (fun n : ℕ => 2*sqrt A * sqrt (sqrt (2*j^2*A^2/(n:ℝ)))) atTop (𝓝 0) := by
  have hd : Tendsto (fun n : ℕ => 2*j^2*A^2/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (2*j^2*A^2)
  simpa only [sqrt_zero, mul_zero, Function.comp_def] using
    (tendsto_const_nhds.mul (Real.continuous_sqrt.continuousAt.tendsto.comp
      (Real.continuous_sqrt.continuousAt.tendsto.comp hd)))

end SKRatioGaussian

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
