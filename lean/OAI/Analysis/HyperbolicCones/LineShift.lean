import OAI.Analysis.HyperbolicCones.PolynomialScaling
import OAI.Analysis.HyperbolicCones.LineEvaluation

namespace OAI

noncomputable section

namespace Paper256

theorem linePolynomial_eval (x : Ambient) (t : ℝ) :
    (linePolynomial x).eval t =
      MvPolynomial.eval (coordinates (t • basePoint - x)) polynomial := by
  rw [coordinates_sub, coordinates_smul]
  change (Polynomial.evalRingHom t) ((MvPolynomial.eval₂Hom Polynomial.C
    (fun i => Polynomial.C (coordinates basePoint i) * Polynomial.X -
      Polynomial.C (coordinates x i))) polynomial) =
    (MvPolynomial.eval₂Hom (RingHom.id ℝ)
      (t • coordinates basePoint - coordinates x)) polynomial
  rw [MvPolynomial.map_eval₂Hom]
  congr 2
  · ext r
    simp
  · ext i
    simp only [Polynomial.coe_evalRingHom, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm]

theorem linePolynomial_eval_neg (x : Ambient) (t : ℝ) :
    (linePolynomial x).eval (-t) =
      MvPolynomial.eval (coordinates (x + t • basePoint)) polynomial := by
  rw [linePolynomial_eval]
  have h : (-t) • basePoint - x = -(x + t • basePoint) := by
    simp [neg_add_rev, sub_eq_add_neg]
  rw [h, polynomial_eval_neg]

theorem real_aeval (p : Polynomial ℝ) (t : ℝ) :
    p.aeval (t : ℂ) = Complex.ofReal (p.eval t) :=
  Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval t p

end Paper256

end

end OAI
