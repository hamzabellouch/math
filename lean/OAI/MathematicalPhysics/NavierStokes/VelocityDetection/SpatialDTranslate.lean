import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.Model

namespace OAI

noncomputable section
namespace VelocityDetection
open scoped BigOperators Topology ContDiff
open Set Function Filter

theorem spatialD_translate {n : ℕ} (i : Fin n) (q : ScalarField n) (c : ℝ → Coord n) :
    spatialD i (fun t X => q t (X - c t)) = fun t X => spatialD i q t (X - c t) := by
  funext t X
  have h (s : ℝ) : update X i s - c t = update (X - c t) i (s - c t i) := by
    ext j
    by_cases hj : j = i
    · subst j; simp
    · simp [update_of_ne hj]
  simp only [spatialD, h]
  exact deriv_comp_sub_const (fun r => q t (update (X - c t) i r)) (c t i) (X i)

theorem laplacian_translate {n : ℕ} (q : ScalarField n) (c : ℝ → Coord n) (t : ℝ)
    (X : Coord n) :
    laplacian (fun t X => q t (X - c t)) t X = laplacian q t (X - c t) := by
  simp only [laplacian, spatialD_translate]

theorem spatialD_eq_fderiv {n : ℕ} (i : Fin n) {q : ScalarField n} (t : ℝ)
    (X : Coord n) (hq : DifferentiableAt ℝ (q t) X) :
    spatialD i q t X = fderiv ℝ (q t) X (Pi.single i 1) := by
  have hq' : DifferentiableAt ℝ (q t) (update X i (X i)) := by simpa using hq
  simpa [spatialD, Function.comp_def] using
    (hq'.hasFDerivAt.comp_hasDerivAt (X i) (hasDerivAt_update X i (X i))).deriv

end VelocityDetection
end

end OAI
