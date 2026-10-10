import OAI.Geometry.SurfaceImmersion.Correction.PolynomialVariationBounds

namespace OAI

/-! Multilinear scaling of the three actual polynomial variations. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression

namespace MixedExpression

def rescale (G : Fin 4 → Base → Space) (c : Fin 3 → ℝ) : Fin 4 → Base → Space :=
  ![G 0, fun p => c 0 • G 1 p, fun p => c 1 • G 2 p, fun p => c 2 • G 3 p]

lemma rescale_base (G : Fin 4 → Base → Space) (c : Fin 3 → ℝ) : rescale G c 0 = G 0 := rfl

lemma rescale_smooth {G : Fin 4 → Base → Space} (hG : ∀ i, ContDiff ℝ ∞ (G i))
    (c : Fin 3 → ℝ) : ∀ i, ContDiff ℝ ∞ (rescale G c i) := by
  intro i
  fin_cases i
  · exact hG 0
  · exact ContDiff.const_smul (c 0) (hG 1)
  · exact ContDiff.const_smul (c 1) (hG 2)
  · exact ContDiff.const_smul (c 2) (hG 3)

lemma rescale_eq (G : Fin 4 → Base → Space) (c : Fin 3 → ℝ) :
    rescale G c = scaleSlot (scaleSlot (scaleSlot G 0 (c 0)) 1 (c 1)) 2 (c 2) := by
  funext i p
  fin_cases i <;> simp [rescale, scaleSlot]

lemma eval_rescale {e : MixedExpression} {n : Fin 3 → ℕ}
    (he : ∀ j, DegreeIn j e (n j)) {G : Fin 4 → Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (c : Fin 3 → ℝ) (z : Base × ℝ) :
    e.eval (rescale G c) z =
      (c 0 ^ n 0 * c 1 ^ n 1 * c 2 ^ n 2) * e.eval G z := by
  rw [rescale_eq, (he 2).eval_scaleSlot
    (scaleSlot_smooth (scaleSlot_smooth hG 0 (c 0)) 1 (c 1)),
    (he 1).eval_scaleSlot (scaleSlot_smooth hG 0 (c 0)), (he 0).eval_scaleSlot hG]
  ring

end MixedExpression
namespace Expression

lemma variations_degree (e : Expression) (i j : Fin 3) :
    DegreeIn j (e.variations i) (if j ≤ i then 1 else 0) := by
  have h₀ := degree_ofExpression j e
  have h₁ := h₀.differentiate 0
  have h₂ := h₁.differentiate 1
  have h₃ := h₂.differentiate 2
  fin_cases i <;> fin_cases j <;> simp_all [variations]

lemma variations_rescale (e : Expression) {G : Fin 4 → Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (c : Fin 3 → ℝ) (z : Base × ℝ) (i : Fin 3) :
    (e.variations i).eval (rescale G c) z =
      (c 0 * (if 1 ≤ i then c 1 else 1) * (if 2 ≤ i then c 2 else 1)) *
        (e.variations i).eval G z := by
  have h := eval_rescale (fun j => e.variations_degree i j) hG c z
  fin_cases i <;> simpa using h

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
