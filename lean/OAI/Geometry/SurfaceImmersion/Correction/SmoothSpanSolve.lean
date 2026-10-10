import OAI.Geometry.SurfaceImmersion.Correction.PeriodicCorrector

namespace OAI

/-! Smooth dependence of the two-by-two Gram solve used by each corrector. -/

noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.PeriodicCorrector

variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem contDiff_gramDet {Y C : A → E} (hY : ContDiff ℝ ∞ Y) (hC : ContDiff ℝ ∞ C) :
    ContDiff ℝ ∞ (fun p => gramDet (Y p) (C p)) :=
  ((hY.inner ℝ hY).mul (hC.inner ℝ hC)).sub ((hY.inner ℝ hC).pow 2)

theorem contDiff_spanSolve {Y C : A → E} {a : A → ℝ × ℝ}
    (hY : ContDiff ℝ ∞ Y) (hC : ContDiff ℝ ∞ C) (ha : ContDiff ℝ ∞ a)
    (hD : ∀ p, gramDet (Y p) (C p) ≠ 0) :
    ContDiff ℝ ∞ (fun p => spanSolve (Y p) (C p) (a p)) := by
  have hd := contDiff_gramDet hY hC
  change ContDiff ℝ ∞ (fun p =>
    ((inner ℝ (C p) (C p) * (a p).1 - inner ℝ (Y p) (C p) * (a p).2) /
      gramDet (Y p) (C p)) • Y p +
    ((inner ℝ (Y p) (Y p) * (a p).2 - inner ℝ (Y p) (C p) * (a p).1) /
      gramDet (Y p) (C p)) • C p)
  exact ((((hC.inner ℝ hC).mul ha.fst).sub ((hY.inner ℝ hC).mul ha.snd)).div hd hD).smul hY |>.add
    (((((hY.inner ℝ hY).mul ha.snd).sub ((hY.inner ℝ hC).mul ha.fst)).div hd hD).smul hC)

end ClosedSurfaceR4.PeriodicCorrector

end

end OAI
