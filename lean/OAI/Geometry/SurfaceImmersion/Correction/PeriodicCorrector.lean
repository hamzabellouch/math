import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicCalculus

namespace OAI

/-!
The two components of the finite periodic corrector: the explicit solve in
span(Y,C), and integration of the covariance correction in its orthogonal
complement.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.PeriodicCorrector

open CovarianceCorrector PeriodicCalculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def gramDet (Y C : E) : ℝ :=
  inner ℝ Y Y * inner ℝ C C - (inner ℝ Y C) ^ 2

/-- The vector in span(Y,C) with prescribed pairings with Y and C. -/
def spanSolve (Y C : E) : (ℝ × ℝ) →L[ℝ] E :=
  LinearMap.toContinuousLinearMap {
    toFun := fun a =>
      ((inner ℝ C C * a.1 - inner ℝ Y C * a.2) / gramDet Y C) • Y +
      ((inner ℝ Y Y * a.2 - inner ℝ Y C * a.1) / gramDet Y C) • C
    map_add' := by intros; dsimp; module
    map_smul' := by intros; dsimp; module }

omit [CompleteSpace E] in
lemma spanSolve_pairings (Y C : E) (hD : gramDet Y C ≠ 0) (a : ℝ × ℝ) :
    inner ℝ Y (spanSolve Y C a) = a.1 ∧
      inner ℝ C (spanSolve Y C a) = a.2 := by
  change inner ℝ Y (_ • Y + _ • C) = a.1 ∧
    inner ℝ C (_ • Y + _ • C) = a.2
  have hc : inner ℝ C Y = inner ℝ Y C := (real_inner_comm C Y).symm
  simp only [inner_add_right, real_inner_smul_right, hc]
  constructor
  · calc
      _ = a.1 * gramDet Y C / gramDet Y C := by unfold gramDet; ring
      _ = a.1 := mul_div_cancel_right₀ _ hD
  · calc
      _ = a.2 * gramDet Y C / gramDet Y C := by unfold gramDet; ring
      _ = a.2 := mul_div_cancel_right₀ _ hD

lemma average_spanSolve (Y C : E) {H K : Period → ℝ}
    (hH : Continuous H) (hK : Continuous K)
    (hmH : average H = 0) (hmK : average K = 0) :
    average (fun t => spanSolve Y C (H t, K t)) = 0 := by
  have hi := integrable_of_continuous (hH.prodMk hK)
  have he := (spanSolve Y C).integral_comp_comm hi
  have hm : (∫ t, (H t, K t) ∂AddCircle.haarAddCircle) = (0, 0) := by
    apply Prod.ext
    · have hx := (ContinuousLinearMap.fst ℝ ℝ ℝ).integral_comp_comm hi
      change (∫ t, H t ∂AddCircle.haarAddCircle) =
        (∫ t, (H t, K t) ∂AddCircle.haarAddCircle).1 at hx
      exact hx.symm.trans hmH
    · have hx := (ContinuousLinearMap.snd ℝ ℝ ℝ).integral_comp_comm hi
      change (∫ t, K t ∂AddCircle.haarAddCircle) =
        (∫ t, (H t, K t) ∂AddCircle.haarAddCircle).2 at hx
      exact hx.symm.trans hmK
  change (∫ t, spanSolve Y C (H t, K t) ∂AddCircle.haarAddCircle) = 0
  rw [he, hm]
  exact (spanSolve Y C).map_zero

lemma average_fluctuation {r : Period → ℝ} (hr : Continuous r) :
    average (fluctuation r) = 0 := by
  change CovarianceCorrector.average (fun t => r t - CovarianceCorrector.average r) = 0
  rw [average_sub hr continuous_const, CovarianceCorrector.average_const, sub_self]

/-- A mean-zero prescribed fluctuation is realized by the angular derivative
of an actual smooth mean-zero periodic function. -/
theorem exists_integrated_covariance [FiniteDimensional ℝ E]
    {V : Period → E} (hV : Continuous V) {v : E} (hv : average V = v)
    {r : Period → ℝ} (hr : Continuous r) (hr0 : average r = 0)
    (hVs : ContDiff ℝ ∞ (fun t : ℝ => V (t : Period)))
    (hrs : ContDiff ℝ ∞ (fun t : ℝ => r (t : Period)))
    {q : ℝ} (hq : 0 < q) (hcircle : ∀ t, inner ℝ (V t) (V t) = q) :
    ∃ Z W : Period → E, Continuous Z ∧ Continuous W ∧
      ContDiff ℝ ∞ (fun t : ℝ => Z (t : Period)) ∧
      ContDiff ℝ ∞ (fun t : ℝ => W (t : Period)) ∧
      average Z = 0 ∧ average W = 0 ∧
      (∀ t : ℝ, HasDerivAt (fun s : ℝ => Z (s : Period)) (W (t : Period)) t) ∧
      fluctuation (fun t => inner ℝ (V t) (W t)) = r := by
  obtain ⟨W, hW, hWs, hW0, hsolve⟩ :=
    exists_smooth_covariance_corrector hV hv hr hr0 hVs hrs hq hcircle
  obtain ⟨Z, hZ, hZs, hZ0, hZd⟩ := exists_circle_primitive hWs hW0
  exact ⟨Z, W, hZ, hW, hZs, hWs, hZ0, hW0, hZd, hsolve⟩

omit [CompleteSpace E] in
/-- Differentiating the first pairing gives the second slow constraint used
in the triangular system, because Y_y=C. -/
theorem slow_pairing_constraint {Y U : ℝ → E} {H : ℝ → ℝ}
    {y : ℝ} {C U' : E} {H' j : ℝ}
    (hY : HasDerivAt Y C y) (hU : HasDerivAt U U' y)
    (hH : HasDerivAt H H' y)
    (he : ∀ t, inner ℝ (Y t) (U t) = H t)
    (hC : inner ℝ C (U y) = H' - j) :
    inner ℝ (Y y) U' = j := by
  have hd := hY.inner ℝ hU
  have heq : (fun t => inner ℝ (Y t) (U t)) = H := funext he
  rw [heq] at hd
  have hu := hd.unique hH
  linarith

end ClosedSurfaceR4.PeriodicCorrector

end

end OAI
