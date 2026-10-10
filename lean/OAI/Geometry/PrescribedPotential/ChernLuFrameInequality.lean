import Mathlib
import OAI.Geometry.PrescribedPotential.FrameCompactBounds
import OAI.Geometry.PrescribedPotential.FrameSecondCalculus
import OAI.Geometry.PrescribedPotential.MatrixFrameNormalization
import OAI.Geometry.PrescribedPotential.ScalarFrameCalculus

namespace OAI

/-! Chern Lu Frame Inequality. -/

section

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}

lemma inverseTrace_log_inequality_frame [Nonempty (Fin n)]
    {U : Set (V n)} (hU : IsOpen U)
    (B : V n →L[ℂ] V n) (hB : IsUnit (frameMatrix B))
    {M G : V n → Matrix (Fin n) (Fin n) ℂ} (hM : ContDiffOn ℝ ∞ M U)
    (hp : ∀ y ∈ U, (M y).PosDef)
    (hclosed : ∀ y ∈ U, ∀ u v w : V n,
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (M q) v w) y u +
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (M q) w u) y v +
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (M q) u v) y w = 0)
    (hG : ContDiffOn ℝ ∞ G U) (hGp : ∀ y ∈ U, (G y).PosDef)
    {w : V n} (hw : B w ∈ U) (hM1 : pullMetric B M w = 1) :
    frameResidual (PotentialKaehler.potentialMatrix (fun y => Real.log (M y).det.re) (B w))
      (G (B w)) (curvatureDiagonal G (B w)) (frameMatrix B) ≤
      inverseTrace M G (B w) *
        (PotentialKaehler.potentialMatrix (fun y => Real.log (inverseTrace M G (B y))) w).trace.re := by
  have hi := inverseTrace_log_inequality_at_one (hU.preimage B.continuous)
    (pullMetric_smooth hU B hM) (pullMetric_positive B hB hp)
    (pullMetric_closed hU B hM hclosed) (pullMetric_smooth hU B hG) (pullMetric_positive B hB hGp) hw hM1
  rw [potentialMatrix_logdet_pullMetric hU B hB hM hp hw] at hi
  simp_rw [curvatureDiagonal_pullMetric hU B hB hG hw] at hi
  have hs : inverseTrace (pullMetric B M) (pullMetric B G) = fun y => inverseTrace M G (B y) :=
    funext (fun y => inverseTrace_pullMetric B hB M G y)
  rw [hs] at hi
  simpa only [frameResidual,pullMetric,frameMatrix_mulVec] using hi

lemma inverseTrace_eq_frameGram (B : V n →L[ℂ] V n) (hB : IsUnit (frameMatrix B))
    (M G : V n → Matrix (Fin n) (Fin n) ℂ) (w : V n) (hM1 : pullMetric B M w = 1) :
    inverseTrace M G (B w) = frameGram (G (B w)) (frameMatrix B) := by
  rw [← inverseTrace_pullMetric B hB M G w]
  unfold inverseTrace
  rw [hM1,inv_one,one_mul]
  rfl
end KaehlerCalculus

end
end

end OAI
