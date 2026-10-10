import OAI.Analysis.MetricEntropy.LabelEncoding
import OAI.Analysis.MetricEntropy.CompressionCode
import OAI.Analysis.MetricEntropy.WeightRounding
import OAI.Analysis.MetricEntropy.CompressionLevels
import OAI.Analysis.MetricEntropy.LogProfile

namespace OAI

universe uX uLabel

/-!
# The fixed decoded family of compression approximants

The decoder uses only shared partition data, fixed label representatives, and
the finite code. Original column centers and coefficient vectors are absent
from its arguments. Every subset of the partition indices receives a weight
slot, so the enumeration includes every admissible-family encoding.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators

variable {X : Type uX} {u q : ℕ} {Label : Fin u → Type uLabel}

/-- Decode the common index, pivot labels, and rounded grouped weights into
an actual real-valued function on the original domain. -/
def compressionDecode (L : (i : Fin u) → X → Label i) (E : FixedLabels L q)
    (h s : ℕ) (θ : ℝ)
    (code : CompressionCode u q h s (weightCodeSize (roundingStep θ s u))) : X → ℝ :=
  fun x => ∑ j : Fin h, LogProfile.gamma h j.val *
    ∑ k : Fin s, ∑ T : Finset (Fin u),
      decodeWeight (roundingStep θ s u) (code.2.2 j k T) *
        CompressionLevels.ballIndicator L T (2 * j.val + 1) x
          (E.representative code.1 (code.2.1 j k))

/-- The actual finite family, fixed before choosing a coefficient vector. -/
def compressionList (L : (i : Fin u) → X → Label i) (E : FixedLabels L q)
    (h s : ℕ) (θ : ℝ) : Finset (X → ℝ) :=
  compressionImage (compressionDecode L E h s θ)

theorem mem_compressionList (L : (i : Fin u) → X → Label i) (E : FixedLabels L q)
    (h s : ℕ) (θ : ℝ) (a : X → ℝ) :
    a ∈ compressionList L E h s θ ↔
      ∃ code : CompressionCode u q h s (weightCodeSize (roundingStep θ s u)),
        compressionDecode L E h s θ code = a :=
  mem_compressionImage _ _

/-- Every encoded construction is included in the one shared finite list. -/
theorem compressionDecode_mem_compressionList
    (L : (i : Fin u) → X → Label i) (E : FixedLabels L q) (h s : ℕ) (θ : ℝ)
    (code : CompressionCode u q h s (weightCodeSize (roundingStep θ s u))) :
    compressionDecode L E h s θ code ∈ compressionList L E h s θ :=
  decode_mem_compressionImage _ code

/-- The finite family is nonempty for positive index and label counts. The
rounded-weight alphabet is always nonempty, even at degenerate meshes. -/
theorem compressionList_nonempty
    (L : (i : Fin u) → X → Label i) (E : FixedLabels L q) (h s : ℕ) (θ : ℝ)
    (hu : 0 < u) (hq : 0 < q) : (compressionList L E h s θ).Nonempty :=
  compressionImage_nonempty _ hu hq (weightCodeSize_pos _)

/-- First count with the exact integer size of the rounded-weight alphabet. -/
theorem compressionList_card_le_nat
    (L : (i : Fin u) → X → Label i) (E : FixedLabels L q) (h s : ℕ) (θ : ℝ) :
    (compressionList L E h s θ).card ≤
      u * q ^ (h * s) * weightCodeSize (roundingStep θ s u) ^ (h * s * 2 ^ u) :=
  card_compressionImage_le _

/-- The real cardinality bound, with no factor involving the
size of `X`, original pivots, or column centers. -/
theorem compressionList_card_le
    (L : (i : Fin u) → X → Label i) (E : FixedLabels L q) (h s : ℕ) (θ : ℝ)
    (hθ : 0 < θ) (hs : 0 < s) :
    ((compressionList L E h s θ).card : ℝ) ≤
      (u : ℝ) * (q : ℝ) ^ (h * s) *
        (1 + (s : ℝ) * 2 ^ u / θ) ^ (h * s * 2 ^ u) := by
  have hsize : (weightCodeSize (roundingStep θ s u) : ℝ) ≤
      1 + (s : ℝ) * 2 ^ u / θ := by
    simpa only [roundingStep, one_div_div] using
      (weightCodeSize_le (roundingStep_pos (u := u) hθ hs))
  calc
    ((compressionList L E h s θ).card : ℝ) ≤
        (u : ℝ) * (q : ℝ) ^ (h * s) *
          (weightCodeSize (roundingStep θ s u) : ℝ) ^ (h * s * 2 ^ u) := by
      exact_mod_cast compressionList_card_le_nat L E h s θ
    _ ≤ (u : ℝ) * (q : ℝ) ^ (h * s) *
        (1 + (s : ℝ) * 2 ^ u / θ) ^ (h * s * 2 ^ u) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hsize _)
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))

end MetricEntropyDuality

end

end OAI
