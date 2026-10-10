import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactCalibration
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceGeometryBounds

namespace OAI

/-! The literal rounded source, rather than an arbitrary bounded graph,
admits one common polynomial calibration scale and polynomial coordinate
extent.  The scale exponent may also meet any fixed analytic lower bound. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb.SourceMetadataProgram
open ContactMediator MediatorIteration

def calibrationSize (d : BinaryHeisenberg) : ℝ :=
  (binaryHeisenbergCodec.encode d).length + 2

abbrev geometricWeight (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :=
  (finalGraph (geometricSource k d h).bonds
    (roundingDenominator k d + size d ^ k + 1) (size d ^ k)).weight

abbrev geometricGraph (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid) :=
  finalGraph (geometricSource k d h).bonds
    (roundingDenominator k d + size d ^ k + 1) (size d ^ k)

theorem exists_source_calibration {freq : ℝ} (hfreq : 0 < freq)
    (k B : ℕ) (minimum : ℝ) :
    ∃ exponent : ℕ, 0 < exponent ∧ minimum ≤ (exponent : ℝ) ∧
      ∀ (d : BinaryHeisenberg) (h : d.Valid), d.PolynomialPromise k →
        ∃ u : GlobalSite (geometricSource k d h) → PlanarPosition,
          (∀ a, calibrationSize d ^ exponent *
              planarHopping ‖u ((geometricGraph k d h).left a) -
                u ((geometricGraph k d h).right a)‖ =
            coulombHoppingTarget freq (calibrationSize d ^ B)⁻¹ (geometricWeight k d h a)
              ‖u ((geometricGraph k d h).left a) - u ((geometricGraph k d h).right a)‖) ∧
          (∀ x y, x ≠ y →
            (1 - contactLengthTolerance) * ((exponent : ℝ) * Real.log (calibrationSize d)) ≤
              ‖u x - u y‖) ∧
          (∀ x y, x ≠ y → Nonedge (geometricSource k d h)
            (roundingDenominator k d + size d ^ k + 1) (size d ^ k) x y →
              (6 / 5) * ((exponent : ℝ) * Real.log (calibrationSize d)) < ‖u x - u y‖) ∧
          (∀ c : GlobalSite (geometricSource k d h) → ℝ,
            localizedGramConstant freq * ∑ i, c i ^ 2 ≤
            ∑ i, ∑ j, localizedCoulombCoeff freq (u i) (u j) * c i * c j) ∧
          Function.Injective u ∧
          (∀ x i, |u x i| ≤ calibrationSize d ^ (exponent + k + 7)) := by
  obtain ⟨A, _, hweight⟩ := geometricSource_weight_range k
  obtain ⟨exponent, he, hminimum, hcal⟩ :=
    exists_calibrated_finalGraph_above hfreq A B 6 minimum
  refine ⟨exponent, he, hminimum, fun d h hp => ?_⟩
  have hN : 2 ≤ calibrationSize d := by
    unfold calibrationSize
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hw := hweight d h hp
  obtain ⟨u, hlink, hsep, hnon, hgram, hinj, hext⟩ :=
    (hcal (calibrationSize d) hN).2 (geometricSource k d h)
      (roundingDenominator k d + size d ^ k + 1) (size d ^ k)
      (fun a => (geometricWeight k d h a : ℝ)) (geometricSource_count k d h)
      (fun a => (hw a).1) (fun a => (hw a).2)
  refine ⟨u, hlink, hsep, hnon, hgram, hinj, ?_⟩
  intro x i
  exact (hext (calibrationSize d ^ k) (geometricSource_coordinates k d h hp) x i).trans
    (logarithmic_extent_polynomial exponent k hN)

end ContinuumCoulomb.SourceMetadataProgram

end

end OAI
