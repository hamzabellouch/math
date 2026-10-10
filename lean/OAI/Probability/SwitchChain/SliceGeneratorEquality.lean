import OAI.Probability.SwitchChain.SliceGeneratorSampling
import OAI.Probability.SwitchChain.SliceEquality
import OAI.Probability.SwitchChain.SliceMoments

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem315.SliceEuclideanGenerator

variable {α : Type*} [Fintype α] [DecidableEq α]

def equalityVector (q : ℕ) (p : ℝ) (i j : α) : EuclideanSpace ℝ (State α q) :=
  sample q (fun x => SliceEquality.offDiagonal (SliceEquality.centeredEquality x p) i j)

theorem equalityVector_apply (q : ℕ) (p : ℝ) (i j : α) (S : State α q) :
    equalityVector q p i j S =
      if i = j then 0 else SliceMoments.equalIndicator i j S.val - p := by
  by_cases hij : i = j
  · simp [equalityVector, sample, SliceEquality.offDiagonal, hij]
  · by_cases hi : i ∈ S.val <;> by_cases hj : j ∈ S.val <;>
      simp [equalityVector, sample, SliceEquality.offDiagonal, hij,
        SliceEquality.centeredEquality, SliceEquality.equalityIndicator,
        coordinates, SliceMoments.equalIndicator, hi, hj]

theorem additive_equality_image (q : ℕ) (p : ℝ) (u : α → ℝ) (hu : ∑ i, u i = 0) :
    (∑ i, ∑ j, (u i + u j) • equalityVector q p i j) =
      (2 * (2 * (q : ℝ) - (Fintype.card α : ℝ))) •
        sample q (fun x => ∑ i, u i * x i) := by
  ext S
  have h := SliceEquality.additive_centeredEquality_image (coordinates S)
    (coordinates_binary S) (q : ℝ) p (coordinates_sum S) u hu
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
    equalityVector, sample_apply]
  linarith

theorem rowzero_equality_image (q : ℕ) (p : ℝ) (c : α → α → ℝ)
    (hdiag : ∀ i, c i i = 0) (hrow : ∀ i, ∑ j, c i j = 0)
    (hcol : ∀ j, ∑ i, c i j = 0) :
    (∑ i, ∑ j, c i j • equalityVector q p i j) =
      (2 : ℝ) • sample q (fun x => ∑ i, ∑ j, c i j * (x i * x j)) := by
  ext S
  have h := SliceEquality.row_zero_offDiagonal_centeredEquality_image (coordinates S)
    (coordinates_binary S) p c hdiag hrow hcol
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
    equalityVector, sample_apply]
  linarith

theorem generator_additive_equality (q : ℕ) (p : ℝ) (u : α → ℝ) (hu : ∑ i, u i = 0) :
    generator q (∑ i, ∑ j, (u i + u j) • equalityVector q p i j) =
      ((Fintype.card α : ℝ) / 2) • (∑ i, ∑ j, (u i + u j) • equalityVector q p i j) := by
  rw [additive_equality_image q p u hu, map_smul, generator_sample_linear q u hu]
  simp only [smul_smul]
  congr 1
  ring

theorem generator_rowzero_equality (q : ℕ) (p : ℝ) (c : α → α → ℝ)
    (hdiag : ∀ i, c i i = 0) (hrow : ∀ i, ∑ j, c i j = 0)
    (hcol : ∀ j, ∑ i, c i j = 0) :
    generator q (∑ i, ∑ j, c i j • equalityVector q p i j) =
      ((Fintype.card α : ℝ) - 1) • (∑ i, ∑ j, c i j • equalityVector q p i j) := by
  rw [rowzero_equality_image q p c hdiag hrow hcol, map_smul,
    generator_sample_quadratic q c hdiag hrow hcol]
  simp only [smul_smul]
  congr 1
  ring

end Problem315.SliceEuclideanGenerator

end

end OAI
