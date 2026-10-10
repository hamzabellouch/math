import Mathlib
import OAI.Probability.SKRatio.Matrices.UnitBall
import OAI.Probability.SKRatio.Matrices.GaussianProductUpperTailLipschitz
import OAI.Probability.SKRatio.Matrices.DiagonalSum

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
