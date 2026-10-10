import Mathlib
import OAI.Probability.SKGap.Localization.UnitBall
import OAI.Probability.SKGap.Gaussian.GaussianProductUpperTailLipschitz

namespace OAI

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
namespace SKGap
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

end SKGap

namespace SKGap
section DiagonalProbability
open MeasureTheory ProbabilityTheory Real Set Filter
variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma scaled_diagonal_expected_margin {j A : ℝ} {a : ι → ℝ}
    (hj : 0 ≤ j) (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) (hA0 : 0 ≤ A)
    (hsub : sqrt j*A ≤ 1) :
    (∫ g, diagonalProcess (j/(Fintype.card ι:ℝ)) a 1
      ((j/(Fintype.card ι:ℝ))*∑ i, a i) g
      ∂gaussianCoordinates (MatrixCoordinates ι)) ≤
      1-(1-sqrt j*A)^2 +
        2*sqrt A*sqrt (sqrt (2*j^2*A^2/(Fintype.card ι:ℝ))) := by
  have h := diagonalProcess_expected_margin (div_nonneg hj (by positivity)) ha hA hA0
    (by norm_num : (0:ℝ) ≤ 1) le_rfl (scaled_sqrt_mean_bound hj ha hA hA0) hsub
  exact h.trans (add_le_add_right
    (mul_le_mul_of_nonneg_left (sqrt_le_sqrt (sqrt_le_sqrt
      (scaled_variance_bound (j := j) ha hA))) (show 0 ≤ 2*sqrt A by positivity)) _)

theorem scaled_diagonal_path_tail {j A : ℝ} {a : ι → ℝ}
    (hj : 0 < j) (hA0 : 0 < A) (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A)
    (hsub : sqrt j*A < 1)
    (herr : 2*sqrt A*sqrt (sqrt (2*j^2*A^2/(Fintype.card ι:ℝ))) ≤
      (1-sqrt j*A)^2/4) :
    (gaussianCoordinates (MatrixCoordinates ι)).real
      {g | ∃ z ∈ Icc (0:ℝ) 1,
        1-(1-sqrt j*A)^2/2 < diagonalProcess (j/(Fintype.card ι:ℝ)) a z
          ((j/(Fintype.card ι:ℝ))*∑ i, a i) g} ≤
      Real.exp (-((1-sqrt j*A)^2)^2 * (Fintype.card ι:ℝ) / (16*π^2*j*A^2)) := by
  let r := j/(Fintype.card ι:ℝ)
  let q := r*∑ i, a i
  let δ := (1-sqrt j*A)^2
  let c := 1-δ/2
  let P := diagonalProcess r a 1 q
  have hn : 0 < (Fintype.card ι:ℝ) := by exact_mod_cast Fintype.card_pos
  have hr : 0 < r := div_pos hj hn
  have hq : 0 ≤ q := mul_nonneg hr.le (Finset.sum_nonneg (fun i _ => ha i))
  have hd : 0 < δ := sq_pos_of_pos (sub_pos.mpr hsub)
  have hd1 : δ ≤ 1 := by
    dsimp [δ]
    have hb : 0 ≤ sqrt j*A := by positivity
    nlinarith
  have hc : 0 ≤ c := by dsimp [c]; linarith
  have hqc : q*A ≤ c := scaled_qA_bound hj.le hA hA0.le hsub.le
  have hmean : (∫ g, P g ∂gaussianCoordinates (MatrixCoordinates ι)) ≤ 1-3*δ/4 := by
    have h := scaled_diagonal_expected_margin hj.le ha hA hA0.le hsub.le
    change (∫ g, P g ∂gaussianCoordinates (MatrixCoordinates ι)) ≤ 1-δ+_ at h
    change _ ≤ δ/4 at herr
    linarith
  have hlip := diagonalProcess_lipschitz hr.le ha hA hA0.le (by norm_num : (0:ℝ) ≤ 1) q
  have hL : 0 < Real.toNNReal (1*sqrt (2*r)*A) := by
    rw [Real.toNNReal_pos]
    positivity
  have htail := gaussianProduct_upper_tail_lipschitz hlip hL (show 0 ≤ δ/4 by positivity)
  have hset : {g | ∃ z ∈ Icc (0:ℝ) 1, c < diagonalProcess r a z q g} ⊆
      {g | δ/4 ≤ P g - ∫ y, P y ∂gaussianCoordinates (MatrixCoordinates ι)} := by
    rintro g ⟨z, hz, hg⟩
    have hgc : c < P g := by
      by_contra h
      have hpath := diagonalProcess_path_le ha hA hA0.le hq hc hqc
        (le_of_not_gt h) hz.1 hz.2
      exact (not_lt_of_ge hpath) hg
    change δ/4 ≤ _
    dsimp [c] at hgc
    linarith
  refine (measureReal_mono hset).trans (htail.trans_eq ?_)
  congr 1
  rw [Real.coe_toNNReal _ (by positivity)]
  have hs : (sqrt (2*r))^2 = 2*r := sq_sqrt (by positivity)
  simp only [one_mul]
  rw [mul_pow, hs]
  dsimp [δ, r]
  field_simp
  ring

theorem exists_uniform_diagonal_cutoff {j A : ℝ} (hsub : sqrt j*A < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      2*sqrt A*sqrt (sqrt (2*j^2*A^2/(n:ℝ))) ≤ (1-sqrt j*A)^2/4 := by
  have hpos : 0 < (1-sqrt j*A)^2/4 := by positivity
  have h := (diagonal_error_tendsto j A).eventually (gt_mem_nhds hpos)
  obtain ⟨n₀, hn⟩ := eventually_atTop.mp h
  exact ⟨n₀, fun n hn' => (hn n hn').le⟩

end DiagonalProbability
end SKGap

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
