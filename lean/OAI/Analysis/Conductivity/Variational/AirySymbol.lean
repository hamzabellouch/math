import Mathlib
import OAI.Analysis.Conductivity.Variational.DivSymbolTwo
import OAI.Analysis.Conductivity.Scalarization.SmoothScalarAlgebra

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity
open Matrix

def airySymbol (ξ : Fin 3 → ℝ) : Fin 5 → ℝ :=
  ![ξ 1 ^ 2, -(ξ 0 * ξ 1), ξ 0 ^ 2, 0, 0]

def transverseSymbol (ξ : Fin 3 → ℝ) (p q r : ℝ) : Fin 5 → ℝ :=
  ![ξ 2 * p, ξ 2 * q, ξ 2 * r,
    -(ξ 0 * p) - ξ 1 * q, -(ξ 0 * q) - ξ 1 * r]

theorem airy_transverse_span {ξ : Fin 3 → ℝ} (hξ : ξ ≠ 0)
    {F : Fin 5 → ℝ} (hF : divSymbolTwo ξ *ᵥ F = 0) :
    ∃ α p q r : ℝ, F = α • airySymbol ξ + transverseSymbol ξ p q r := by
  have h0 := congr_fun hF 0
  have h1 := congr_fun hF 1
  simp [divSymbolTwo, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1
  by_cases hz : ξ 2 = 0
  · by_cases hx : ξ 0 = 0
    · have hy : ξ 1 ≠ 0 := by
        intro hy
        apply hξ
        funext i
        fin_cases i <;> simp [hx, hy, hz]
      have hb : F 1 = 0 := by simpa [hx, hz, hy] using h0
      have hc : F 2 = 0 := by simpa [hx, hz, hy] using h1
      refine ⟨F 0 / ξ 1 ^ 2, 0, -F 3 / ξ 1, -F 4 / ξ 1, ?_⟩
      funext i
      fin_cases i <;> simp [airySymbol, transverseSymbol, hx, hz, hb, hc, hy] <;> field_simp
    · have hb : ξ 0 * F 1 = -(ξ 1 * F 2) := by
        simp only [hz, zero_mul, add_zero] at h1
        linarith
      have ha : ξ 0 ^ 2 * F 0 = ξ 1 ^ 2 * F 2 := by
        simp only [hz, zero_mul, add_zero] at h0
        nlinarith [congrArg (fun t => ξ 1 * t) hb, congrArg (fun t => ξ 0 * t) h0]
      refine ⟨F 2 / ξ 0 ^ 2, -F 3 / ξ 0 + ξ 1 * F 4 / ξ 0 ^ 2,
        -F 4 / ξ 0, 0, ?_⟩
      funext i
      fin_cases i <;> simp [airySymbol, transverseSymbol, hz] <;>
        field_simp [hx] <;> nlinarith [hb, ha]
  · refine ⟨0, F 0 / ξ 2, F 1 / ξ 2, F 2 / ξ 2, ?_⟩
    funext i
    fin_cases i <;> simp [airySymbol, transverseSymbol] <;>
      field_simp <;> nlinarith [h0, h1]

theorem tsupport_smoothDirection_subset {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : E) (f : SmoothScalar E) :
    tsupport (smoothDirection v f).val ⊆ tsupport f.val := by
  exact (tsupport_comp_subset (g := fun L : E →L[ℝ] ℝ => L v) (by simp)
    (fderiv ℝ f.val)).trans (tsupport_fderiv_subset ℝ)

theorem compactSupport_smoothDirection {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : E) {f : SmoothScalar E} (hf : HasCompactSupport f.val) :
    HasCompactSupport (smoothDirection v f).val :=
  hf.of_isClosed_subset isClosed_closure (tsupport_smoothDirection_subset v f)

end ScalarConductivity

end

end OAI
