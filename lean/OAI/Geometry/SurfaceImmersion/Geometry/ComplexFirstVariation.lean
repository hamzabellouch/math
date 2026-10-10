import OAI.Geometry.SurfaceImmersion.Geometry.ComplexMixedJets
import OAI.Geometry.SurfaceImmersion.Geometry.ComplexJetDecomposition

namespace OAI

/-! The complex polynomial first variation is exactly the complexification
of the actual real differential. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression

def complexDirectionData (G : Base → Space) (H : Base → Fin 4 → ℂ) : JetData :=
  Fin.cases (fun w a p => (jet G w a p : ℂ))
    (fun j w a p => if j = 0 then complexJet H w a p else 0)

lemma evalComplex_sumList {ι : Type*} (l : List ι) (f : ι → MixedExpression)
    (G : Base → Space) (J : JetData) (z : Base × ℝ) :
    (sumList l f).evalComplex G J z = (l.map (fun i => (f i).evalComplex G J z)).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [sumList, evalComplex, List.map_cons, List.sum_cons, ih]

lemma evalComplex_ofExpression (e : Expression) (G : Base → Space)
    (H : Base → Fin 4 → ℂ) (z : Base × ℝ) :
    (ofExpression e).evalComplex G (complexDirectionData G H) z = (e.eval G z : ℂ) := by
  induction e with
  | coeff c => rfl
  | atom w a e ih => simp only [ofExpression, evalComplex, complexDirectionData, Fin.cases_zero,
      ih, Expression.eval, Complex.ofReal_mul]
  | add e f ihe ihf => simp only [ofExpression, evalComplex, ihe, ihf, Expression.eval, Complex.ofReal_add]

lemma complex_coefficient_variation (c : LowJet × ℝ → ℝ) (G : Base → Space)
    (H : Base → Fin 4 → ℂ) (z : Base × ℝ) :
    ((coeff c).differentiate 0).evalComplex G (complexDirectionData G H) z =
      ∑ i : Fin 7 × Fin 4, complexJet H (lowWord i.1) i.2 z.1 *
        (coefficientDerivative c i (lowJet G z.1, z.2) : ℂ) := by
  simp only [differentiate, evalComplex_sumList, evalComplex, complexDirectionData,
    Fin.cases_succ, ↓reduceIte]
  exact Finset.sum_map_toList _ _

private lemma complex_sum_decompose {ι : Type*} [Fintype ι] (a b d : ι → ℝ) :
    (∑ i, ((a i : ℂ) + Complex.I * (b i : ℂ)) * (d i : ℂ)) =
      (∑ i, a i * d i : ℝ) + Complex.I * (∑ i, b i * d i : ℝ) := by
  simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Complex.ofReal_mul, ← Complex.ofReal_sum]

/-- This identity identifies the algebraic complex evaluation with the
actual real differential on the real and imaginary parts separately. -/
theorem complex_first_variation (e : Expression) (G : Base → Space)
    {H : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H) (z : Base × ℝ) :
    ((ofExpression e).differentiate 0).evalComplex G (complexDirectionData G H) z =
      (e.variation G (realField H) z : ℂ) +
        Complex.I * (e.variation G (imagField H) z : ℂ) := by
  induction e with
  | coeff c =>
    rw [ofExpression, complex_coefficient_variation]
    simp_rw [complexJet_decompose hH]
    rw [complex_sum_decompose]
    rw [Expression.variation, Expression.variation,
      coefficient_variation_sum, coefficient_variation_sum]
    rfl
  | atom w a e ih =>
    simp only [ofExpression, differentiate, ↓reduceIte, evalComplex,
      complexDirectionData, Fin.cases_zero, Fin.cases_succ, evalComplex_ofExpression, ih,
      Expression.variation]
    rw [complexJet_decompose hH]
    push_cast
    ring
  | add e f ihe ihf =>
    simp only [ofExpression, differentiate, evalComplex, ihe, ihf, Expression.variation,
      Complex.ofReal_add]
    ring

end ClosedSurfaceR4.JetPolynomial

end

end OAI
