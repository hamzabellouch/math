import OAI.Geometry.SurfaceImmersion.Geometry.ComplexQuadraticVariation
import OAI.Geometry.SurfaceImmersion.Correction.ConjugatedPolynomialOperator

namespace OAI

/-! The real quadratic variation is the sum of its zero and double phases. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression

def realDirectionJets (J : DirectionJets) : DirectionJets := fun w a p => (J w a p).re

lemma starDirectionJets_star (J : DirectionJets) :
    starDirectionJets (starDirectionJets J) = J := by
  funext w a p
  exact star_star _

lemma realDirectionJets_eq (J : DirectionJets) :
    realDirectionJets J = (1 / 2 : ℂ) • (J + starDirectionJets J) := by
  funext w a p
  apply Complex.ext <;> simp [realDirectionJets, starDirectionJets]
  ring

lemma quadraticComplex_real_jets (e : Expression) (G : Base → Space)
    (J : DirectionJets) (z : Base × ℝ) :
    quadraticComplex e G (realDirectionJets J) (realDirectionJets J) z =
      (((quadraticComplex e G J J z).re +
        (quadraticComplex e G J (starDirectionJets J) z).re) / 2 : ℝ) := by
  rw [realDirectionJets_eq, quadraticComplex_smul_left, quadraticComplex_smul_right,
    quadraticComplex_add_left, quadraticComplex_add_right, quadraticComplex_add_right,
    quadraticComplex_star]
  have hcross := quadraticComplex_star e G J (starDirectionJets J) z
  rw [starDirectionJets_star] at hcross
  rw [hcross]
  apply Complex.ext <;> simp
  ring

lemma evalComplex_real_jets (e : MixedExpression) (F : Fin 4 → Base → Space) (z : Base × ℝ) :
    e.evalComplex (F 0) (fun i w a p => (jet (F i) w a p : ℂ)) z = (e.eval F z : ℂ) := by
  induction e with
  | coeff c => rfl
  | atom i w a e ih => simp only [evalComplex, eval, ih, Complex.ofReal_mul]
  | add e f ihe ihf => simp only [evalComplex, eval, ihe, ihf, Complex.ofReal_add]

lemma jet_zero (w : List (Fin 2)) (a : Fin 4) (p : Base) :
    jet (0 : Base → Space) w a p = 0 := by
  exact congrFun (iteratedDirectional_zero (w.map coordinateVector)) p

lemma quadraticComplex_real_fields (e : Expression) (G H K : Base → Space) (z : Base × ℝ) :
    quadraticComplex e G (fun w a p => (jet H w a p : ℂ)) (fun w a p => (jet K w a p : ℂ)) z =
      ((e.variations 1).eval ![G, H, K, 0] z : ℂ) := by
  have he : pairJetData G (fun w a p => (jet H w a p : ℂ)) (fun w a p => (jet K w a p : ℂ)) =
      fun i w a p => (jet (![G, H, K, 0] i) w a p : ℂ) := by
    funext i w a p
    fin_cases i <;> simp [pairJetData, jet_zero]
  change (e.variations 1).evalComplex G _ z = _
  rw [he]
  exact evalComplex_real_jets (e.variations 1) ![G, H, K, 0] z

/-- The factor `1/4` includes the Taylor coefficient `1/2` and the real-mode
splitting. The two terms will become the double and zero phases. -/
theorem half_second_variation_real (e : Expression) (G : Base → Space)
    {H : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H) (z : Base × ℝ) :
    (1 / 2 : ℝ) * (e.variations 1).eval ![G, realField H, realField H, 0] z =
      ((quadraticComplex e G (complexJet H) (complexJet H) z).re +
        (quadraticComplex e G (complexJet H) (starDirectionJets (complexJet H)) z).re) / 4 := by
  have he : (fun w a p => (jet (realField H) w a p : ℂ)) = realDirectionJets (complexJet H) := by
    funext w a p
    exact congrArg Complex.ofReal (complexJet_re hH w a p).symm
  have hh := quadraticComplex_real_jets e G (complexJet H) z
  rw [← he, quadraticComplex_real_fields] at hh
  have hr := congrArg Complex.re hh
  simp only [Complex.ofReal_re] at hr
  linarith

end ClosedSurfaceR4.JetPolynomial

end

end OAI
