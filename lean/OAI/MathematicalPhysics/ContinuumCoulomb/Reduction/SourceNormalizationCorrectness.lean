import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.SourceMetadataProgram

namespace OAI

/-! The machine-normalized source registers are the literal bond family
whose complete positive-spin spectral and promise estimates were proved. -/

namespace ContinuumCoulomb.SourceMetadataProgram
open MediatorListProgram

def roundingDenominator (k : ℕ) (d : BinaryHeisenberg) : ℕ :=
  SourceNormalizedSpectrum.denominator d.edges.length (size d ^ k)

theorem rounded_eq (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    SourceNormalizationProgram.rounded (input k d) =
      SourceNormalizedSpectrum.rounded (d.toSource h) (roundingDenominator k d) := by
  simp only [SourceNormalizationProgram.rounded, input, List.length_map, List.map_map]
  change d.edges.map (fun e => (e.left, e.right,
      SourceCoefficientRounding.coefficient (roundingDenominator k d) e.coefficient.value)) =
    List.ofFn (fun e : Fin d.edges.length => ((d.edges.get e).left, (d.edges.get e).right,
      SourceCoefficientRounding.coefficient (roundingDenominator k d) (d.edges.get e).coefficient.value))
  simpa only [List.get_eq_getElem] using (List.ofFn_getElem_eq_map d.edges
    (fun e => (e.left, e.right,
      SourceCoefficientRounding.coefficient (roundingDenominator k d) e.coefficient.value))).symm

theorem retained_eq (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    SourceNormalizationProgram.retained (input k d) =
      SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d) := by
  unfold SourceNormalizationProgram.retained SourceNormalizedSpectrum.retained
  rw [rounded_eq k d h]

theorem normalized_eq (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    SourceNormalizationProgram.normalized (input k d) =
      (((SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)).length,
        roundingDenominator k d + size d ^ k + 1, size d ^ k, d.coordinate.length),
        SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)) := by
  unfold SourceNormalizationProgram.normalized
  rw [retained_eq k d h]
  simp only [input, List.length_map, roundingDenominator]

theorem size_pos (d : BinaryHeisenberg) : 0 < size d := by
  unfold size
  omega

theorem polynomialPromise_weight (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid)
    (hp : d.PolynomialPromise k) :
    ∀ e, |((d.toSource h).coefficient e : ℝ)| ≤ (size d ^ k : ℕ) := by
  intro e
  simpa only [size, Nat.cast_pow, Nat.cast_add, Nat.cast_one, BinaryHeisenberg.toSource] using
    hp.weight_bound e

theorem polynomialPromise_gap (k : ℕ) (d : BinaryHeisenberg)
    (hp : d.PolynomialPromise k) :
    1 / ((size d ^ k : ℕ) : ℚ) ≤ d.upper.value - d.lower.value := by
  have he : (1 : ℝ) / ((size d ^ k : ℕ) : ℝ) ≤
      ((d.upper.value : ℝ) - (d.lower.value : ℝ)) := by
    simpa only [size, Nat.cast_pow, Nat.cast_add, Nat.cast_one, one_div] using hp.gap_bound
  have hq := Rat.cast_le (K := ℝ).mp
    (show (((1 / ((size d ^ k : ℕ) : ℚ)) : ℚ) : ℝ) ≤
      (((d.upper.value - d.lower.value) : ℚ) : ℝ) by
        simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, Rat.cast_sub] using he)
  exact hq

end ContinuumCoulomb.SourceMetadataProgram

end OAI
