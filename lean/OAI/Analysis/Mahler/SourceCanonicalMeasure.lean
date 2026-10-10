import OAI.Analysis.Mahler.SourceTopCoordinates

namespace OAI

open MeasureTheory Set
namespace Mahler
noncomputable section

lemma measurePreserving_coordinateCast {a b : ℕ} (h : a = b) :
    MeasurePreserving (coordinateCast h) volume volume := by
  subst b
  exact MeasurePreserving.id _

lemma measurePreserving_sourceCoordinates (k : ℕ) :
    MeasurePreserving (sourceCoordinates k) volume volume :=
  (MahlerStokes.measurePreserving_complexCoordinates (k+1)).comp
    (measurePreserving_coordinateCast _)

theorem setIntegral_sourceCoordinates (k : ℕ) (S : Set (ComplexEuclidean (k+1)))
    (f : ComplexEuclidean (k+1) → ℝ) :
    (∫ x in (sourceCoordinates k) ⁻¹' S, f (sourceCoordinates k x)) = ∫ z in S, f z :=
  (measurePreserving_sourceCoordinates k).setIntegral_preimage_emb
    (sourceCoordinates k).toHomeomorph.toMeasurableEquiv.measurableEmbedding f S

lemma radiusSq_coordinateCast {a b : ℕ} (h : a = b) (x : Fin a → ℝ) :
    MahlerStokes.radiusSq (coordinateCast h x) = MahlerStokes.radiusSq x := by
  subst b
  rfl

lemma norm_sourceCoordinates_sq (k : ℕ) (x : Fin ((2*k+1)+1) → ℝ) :
    ‖sourceCoordinates k x‖^2 = MahlerStokes.radiusSq x := by
  change ‖MahlerStokes.complexCoordinates (k+1) (coordinateCast _ x)‖^2 = _
  rw [MahlerStokes.norm_complexCoordinates_sq, radiusSq_coordinateCast]

end
end Mahler

end OAI
