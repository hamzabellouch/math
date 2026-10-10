import OAI.Geometry.SurfaceImmersion.Correction.JetPolynomialLinear
import OAI.Geometry.SurfaceImmersion.Geometry.CovarianceRealOperator

namespace OAI

/-! The actual covariance inversion preserves finite polynomial dependence on
higher jets. Its inverse matrix depends only on the low-jet geometric data. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.Expression
open CovarianceCorrector

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

def covariance (V : LowJet → C(Period, E)) (q : LowJet → ℝ) (L : E →L[ℝ] ℝ)
    (e : Expression) : Expression :=
  e.liftOperator (fun Q f t => L (realCorrector (V Q) (q Q) f t))

lemma smoothCoeffs_covariance {O : Set LowJet} (hO : IsOpen O)
    {V : LowJet → C(Period, E)} {q : LowJet → ℝ}
    (hV : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hq : ContDiffOn ℝ ∞ q O) (hqpos : ∀ Q ∈ O, 0 < q Q)
    (hcircle : ∀ Q ∈ O, ∀ t, inner ℝ (V Q t) (V Q t) = q Q)
    (L : E →L[ℝ] ℝ) {e : Expression} (he : e.SmoothCoeffs O) :
    (e.covariance V q L).SmoothCoeffs O := by
  apply smoothCoeffs_liftOperator _ he
  intro c hc
  exact L.contDiff.comp_contDiffOn (contDiffOn_realCorrector hO hV hq hqpos hcircle hc)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] lemma order_covariance (V : LowJet → C(Period, E)) (q : LowJet → ℝ)
    (L : E →L[ℝ] ℝ) (e : Expression) : (e.covariance V q L).order = e.order :=
  order_liftOperator _ _

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] lemma loss_covariance (V : LowJet → C(Period, E)) (q : LowJet → ℝ)
    (L : E →L[ℝ] ℝ) (e : Expression) : (e.covariance V q L).loss = e.loss :=
  loss_liftOperator _ _

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma eval_covariance {O : Set LowJet} (hO : IsOpen O)
    (V : LowJet → C(Period, E)) (q : LowJet → ℝ) (L : E →L[ℝ] ℝ)
    {e : Expression} (he : e.SmoothCoeffs O) (G : Base → Space)
    {p : Base} (hp : lowJet G p ∈ O) (t : ℝ) :
    (e.covariance V q L).eval G (p, t) =
      L (realCorrector (V (lowJet G p)) (q (lowJet G p)) (fun s => e.eval G (p, s)) t) := by
  apply eval_liftOperator hO _ _ _ he G hp t
  · intro Q _ f g hf hg s
    rw [realCorrector_add _ _ hf hg, map_add]
  · intro Q _ a f s
    rw [realCorrector_smul, map_smul, smul_eq_mul]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Each component of the covariance corrector used in the finite periodic
recursion has an actual polynomial representation with the same order and loss. -/
theorem eval_covariance_periodic {O : Set LowJet} (hO : IsOpen O)
    (V : LowJet → C(Period, E)) (q : LowJet → ℝ) (L : E →L[ℝ] ℝ)
    {e : Expression} (he : e.SmoothCoeffs O) (G : Base → Space)
    (r : Base → C(Period, ℝ)) {p : Base} (hp : lowJet G p ∈ O)
    (hr : ∀ s : ℝ, e.eval G (p, s) = r p (s : Period)) (t : ℝ) :
    (e.covariance V q L).eval G (p, t) =
      L (parameterCorrector (fun x => V (lowJet G x)) r (fun x => q (lowJet G x))
        p (t : Period)) := by
  rw [eval_covariance hO V q L he G hp]
  have heq : (fun s => e.eval G (p, s)) = (fun s : ℝ => r p (s : Period)) := funext hr
  rw [heq]
  exact congrArg L (realCorrector_eq_parameterCorrector (fun x => V (lowJet G x))
    (fun x => q (lowJet G x)) r p t)

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
