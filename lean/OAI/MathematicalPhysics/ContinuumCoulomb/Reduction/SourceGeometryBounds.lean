import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceNormalizedLattice
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourcePositiveBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactExtent

namespace OAI

/-! Polynomial site counts, coordinate extent and coefficient ranges for
the literal normalized source passed to the contact realization. -/

noncomputable section
namespace ContinuumCoulomb.SourceMetadataProgram
open ContactMediator

def geometricSource (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) : SquareLatticeHeisenberg :=
  SourceNormalizedSpectrum.lattice (d.toSource h) (roundingDenominator k d)

@[simp] theorem geometricSource_bonds (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    (geometricSource k d h).bonds =
      SourceNormalizedSpectrum.family (d.toSource h) (roundingDenominator k d) := rfl

private theorem nineteen_mul_le_sixth (L : ℕ) : 19 * L ≤ (L + 2) ^ 6 := by
  have h19 : 19 ≤ (L + 2) ^ 5 :=
    (by norm_num : 19 ≤ 2 ^ 5).trans (Nat.pow_le_pow_left (by omega) 5)
  calc
    19 * L ≤ (L + 2) ^ 5 * (L + 2) := Nat.mul_le_mul h19 (by omega)
    _ = (L + 2) ^ 6 := by ring

theorem geometricSource_count (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :
    (Fintype.card (GlobalSite (geometricSource k d h)) : ℝ) ≤
      ((binaryHeisenbergCodec.encode d).length + 2 : ℝ) ^ 6 := by
  have hc := (positive_graph_count_bound k d h).1
  have hp := hc.trans (nineteen_mul_le_sixth (binaryHeisenbergCodec.encode d).length)
  rw [globalSite_card]
  change ((d.coordinate.length + 18 *
    (SourceNormalizedSpectrum.retained (d.toSource h) (roundingDenominator k d)).length : ℕ) : ℝ) ≤ _
  exact_mod_cast hp

theorem geometricSource_coordinates (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid)
    (hp : d.PolynomialPromise k) (j : Fin (geometricSource k d h).vertices) (i : Fin 2) :
    |(contactGridAxis ((geometricSource k d h).coordinate j) i : ℝ)| ≤
      ((binaryHeisenbergCodec.encode d).length + 2 : ℝ) ^ k := by
  have he := binaryHeisenberg_decoded_extent k d h hp j
  have hpow : ((binaryHeisenbergCodec.encode d).length + 1 : ℝ) ^ k ≤
      ((binaryHeisenbergCodec.encode d).length + 2 : ℝ) ^ k :=
    pow_le_pow_left₀ (by positivity) (by linarith) k
  change |(contactGridAxis ((d.toSource h).coordinate j) i : ℝ)| ≤ _
  fin_cases i
  · exact he.1.trans hpow
  · exact he.2.trans hpow

theorem geometricSource_weight_range (k : ℕ) :
    ∃ A : ℕ, 0 < A ∧ ∀ (d : BinaryHeisenberg) (h : d.Valid), d.PolynomialPromise k →
      ∀ e : GlobalEdge (geometricSource k d h),
        (((binaryHeisenbergCodec.encode d).length + 2 : ℝ) ^ A)⁻¹ ≤
          ((MediatorIteration.finalGraph (geometricSource k d h).bonds
            (roundingDenominator k d + size d ^ k + 1) (size d ^ k)).weight e : ℝ) ∧
        ((MediatorIteration.finalGraph (geometricSource k d h).bonds
            (roundingDenominator k d + size d ^ k + 1) (size d ^ k)).weight e : ℝ) ≤
          ((binaryHeisenbergCodec.encode d).length + 2 : ℝ) ^ A := by
  obtain ⟨A, hA, hweight⟩ := source_positive_weight_range k
  exact ⟨A, hA, hweight⟩

end ContinuumCoulomb.SourceMetadataProgram

end

end OAI
