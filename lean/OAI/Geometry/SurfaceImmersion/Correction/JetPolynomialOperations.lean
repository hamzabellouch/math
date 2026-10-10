import OAI.Geometry.SurfaceImmersion.Correction.JetPolynomialCovariance

namespace OAI

noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.Expression

def neg (e : Expression) : Expression := e.mapCoeff (fun c z => -c z)
def sub (e f : Expression) : Expression := .add e f.neg
def fluct (e : Expression) : Expression := e.sub e.mean

@[simp] lemma eval_neg (e : Expression) (G : Base → Space) (z : Base × ℝ) :
    e.neg.eval G z = -e.eval G z := by
  induction e with
  | coeff c => rfl
  | atom w a e ih => simp only [neg, mapCoeff, eval] at *; rw [ih]; ring
  | add e f ihe ihf => simp only [neg, mapCoeff, eval] at *; rw [ihe, ihf]; ring

@[simp] lemma eval_sub (e f : Expression) (G : Base → Space) (z : Base × ℝ) :
    (e.sub f).eval G z = e.eval G z - f.eval G z := by
  simp only [sub, eval, eval_neg, sub_eq_add_neg]

@[simp] lemma order_neg (e : Expression) : e.neg.order = e.order := order_mapCoeff _ _
@[simp] lemma loss_neg (e : Expression) : e.neg.loss = e.loss := loss_mapCoeff _ _
@[simp] lemma order_sub (e f : Expression) : (e.sub f).order = max e.order f.order := by
  simp only [sub, order, order_neg]
@[simp] lemma loss_sub (e f : Expression) : (e.sub f).loss = max e.loss f.loss := by
  simp only [sub, loss, loss_neg]
@[simp] lemma order_fluct (e : Expression) : e.fluct.order = e.order := by
  simp only [fluct, order_sub, order_mean, max_self]
@[simp] lemma loss_fluct (e : Expression) : e.fluct.loss = e.loss := by
  simp only [fluct, loss_sub, loss_mean, max_self]

lemma smoothCoeffs_neg {O : Set LowJet} {e : Expression} (he : e.SmoothCoeffs O) :
    e.neg.SmoothCoeffs O := smoothCoeffs_map e _ (fun _ hc => hc.neg) he

lemma smoothCoeffs_sub {O : Set LowJet} {e f : Expression}
    (he : e.SmoothCoeffs O) (hf : f.SmoothCoeffs O) : (e.sub f).SmoothCoeffs O :=
  ⟨he, smoothCoeffs_neg hf⟩

lemma smoothCoeffs_fluct {O : Set LowJet} (hO : IsOpen O) {e : Expression}
    (he : e.SmoothCoeffs O) : e.fluct.SmoothCoeffs O :=
  smoothCoeffs_sub he (smoothCoeffs_mean hO he)

lemma eval_fluct {O : Set LowJet} (hO : IsOpen O) {e : Expression}
    (he : e.SmoothCoeffs O) (G : Base → Space) {p : Base} (hp : lowJet G p ∈ O) (t : ℝ) :
    e.fluct.eval G (p, t) = e.eval G (p, t) - ∫ s in (0 : ℝ)..1, e.eval G (p, s) := by
  rw [fluct, eval_sub, eval_mean hO he G hp]

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
