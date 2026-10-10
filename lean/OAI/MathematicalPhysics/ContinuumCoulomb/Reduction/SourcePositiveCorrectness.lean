import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.SourcePositiveProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorFullListCorrectness

namespace OAI

/-! Exact semantics of the computed positive-spin source reduction: the
literal output has the full three-stage matrix and the proved rational
thresholds, including the common coefficient-rounding error. -/

noncomputable section
namespace ContinuumCoulomb.SourcePositiveProgram
open MediatorIteration SourceMetadataProgram

abbrev sourceFamily (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :=
  SourceNormalizedSpectrum.family (d.toSource h) (roundingDenominator k d)

abbrev sourceBound (k : ℕ) (d : BinaryHeisenberg) :=
  roundingDenominator k d + size d ^ k + 1

theorem normalized_literal (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    normalized k d = literalInput (sourceFamily k d h) (sourceBound k d) (size d ^ k) := by
  rw [normalized, normalized_eq k d h]
  unfold literalInput sourceFamily SourceNormalizedSpectrum.family
  rw [bonds_toList]
  rfl

theorem bonds_eq (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    (output k d).bonds =
      (finalGraph (sourceFamily k d h) (sourceBound k d) (size d ^ k)).toList := by
  change MediatorThreeStageProgram.finalBonds (normalized k d) = _
  rw [normalized_literal]
  exact (finalGraph_toList _ _ _).symm

theorem offset_eq (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    offset k d = MediatorIteration.offset (sourceFamily k d h) (sourceBound k d) (size d ^ k) := by
  unfold offset
  rw [normalized_literal, offset_toList]

theorem vertices_eq (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    (output k d).vertices = d.coordinate.length +
      (SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)).length * 2 +
      (SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)).length * 2 * 2 +
      ((SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)).length * 2 +
        (SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)).length * 2 * 2) * 2 := by
  change (normalized k d).1.2.2.2 + 18 * (normalized k d).1.1 = _
  rw [normalized, normalized_eq k d h]
  dsimp only
  omega

def energy (x : Registers) : ℝ := sourceMatrixBottom x.vertices (SourceBondLists.matrix x.vertices x.bonds)

theorem energy_eq (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    energy (output k d) = SourceNormalizedSpectrum.positiveEnergy (d.toSource h) (size d ^ k) (size d ^ k) := by
  unfold energy
  rw [bonds_eq k d h, vertices_eq k d h]
  change sourceMatrixBottom _ (SourceBondLists.matrix _
    (finalGraph (sourceFamily k d h) (sourceBound k d) (size d ^ k)).toList) =
    sourceMatrixBottom _ (finalGraph (sourceFamily k d h) (sourceBound k d) (size d ^ k)).matrix
  exact congrArg (sourceMatrixBottom _)
    (Bonds.matrix_toList (finalGraph (sourceFamily k d h) (sourceBound k d) (size d ^ k)))

theorem lower_eq (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    (output k d).lower = SourceNormalizedSpectrum.lowerThreshold
      (d.toSource h) (size d ^ k) (size d ^ k) d.lower.value := by
  change d.lower.value - offset k d + error k d = _
  rw [offset_eq]
  rfl

theorem upper_eq (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    (output k d).upper = SourceNormalizedSpectrum.upperThreshold
      (d.toSource h) (size d ^ k) (size d ^ k) d.upper.value := by
  change d.upper.value - offset k d - error k d = _
  rw [offset_eq]
  rfl

theorem output_yes (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid)
    (hp : d.PolynomialPromise k)
    (hyes : realSourceGroundEnergy (d.toSource h) ≤ d.lower.value) :
    energy (output k d) ≤ (output k d).lower := by
  rw [energy_eq k d h, lower_eq k d h]
  exact SourceNormalizedSpectrum.source_positive_yes _ (pow_pos (size_pos d) k)
    (polynomialPromise_weight k d h hp) hyes

theorem output_no (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid)
    (hp : d.PolynomialPromise k)
    (hno : (d.upper.value : ℝ) ≤ realSourceGroundEnergy (d.toSource h)) :
    ((output k d).upper : ℝ) ≤ energy (output k d) := by
  rw [energy_eq k d h, upper_eq k d h]
  exact SourceNormalizedSpectrum.source_positive_no _ (pow_pos (size_pos d) k)
    (polynomialPromise_weight k d h hp) hno

theorem output_gap (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid)
    (hp : d.PolynomialPromise k) :
    63 / 64 * (d.upper.value - d.lower.value) ≤ (output k d).upper - (output k d).lower := by
  rw [upper_eq k d h, lower_eq k d h]
  exact SourceNormalizedSpectrum.positive_threshold_gap _ _ _ (polynomialPromise_gap k d hp)

end ContinuumCoulomb.SourcePositiveProgram

end

end OAI
