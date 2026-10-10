import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationRatioBudget
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSourcePairData

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators SchwartzMap FourierTransform
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template TemplateSupportRemoval Arithmetic
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [DecidableEq ι]

def canonicalSourceNormalizedData (k : ℕ) (B V : ℕ → ℤ) (T : ℕ → ℝ)
    (J : ℤ) (j : ℕ) (b c : Bool) (s v : ℤ) (e f : Expressions (ι:=ι) k j)
    (t u : HistoryReconstruction.Tree j) (i : ι) (x : Other i → ℤ) (r : ℤ)
    (gate : Bool) (X Δ Wp Wl H : ℝ) (D : ℕ) (copy : Expr ι) (Tc Wc : ℝ) :=
  multiplyData (ratioExpressionData i x copy Tc (-Wc) Wc)
    (canonicalSourcePairData k B V T J j b c s v e f t u i x r gate X Δ Wp Wl H D)

theorem canonicalSourceNormalizedData_ranges (k : ℕ) (B V : ℕ → ℤ) (T : ℕ → ℝ)
    (J : ℤ) (j : ℕ) (b c : Bool) (s v : ℤ) (e f : Expressions (ι:=ι) k j)
    (t u : HistoryReconstruction.Tree j) (i : ι) (x : Other i → ℤ) (r : ℤ)
    (gate : Bool) {X Δ Wp Wl H : ℝ} (hX : 0 < X) (D : ℕ) (copy : Expr ι)
    (Tc Wc : ℝ) (hWc : 0 ≤ Wc) (hc : copy.Valid)
    (he : ∀a z,HistoryReconstruction.Good a (e z))
    (hf : ∀a z,HistoryReconstruction.Good a (f z)) (ρ : 𝓢(ℝ,ℂ)) :
    (canonicalSourceNormalizedData k B V T J j b c s v e f t u i x r gate
      X Δ Wp Wl H D copy Tc Wc).Ranges ρ
      (Sum.elim (fun _=>-Wc) (fun _=>coarseLower D H Δ Wl))
      (Sum.elim (fun _=>Wc) (fun _=>-Δ+Wl))
      (max (Real.exp Wc) (Real.exp ((-Δ+Wl)/2)*leafProfileBound ρ)) := by
  apply multiplyData_ranges
  · exact ranges_mono_bound _ ρ (ratioExpressionData_ranges i x copy Tc (-Wc) Wc (by linarith) hc ρ)
      (le_max_left _ _)
  · exact ranges_mono_bound _ ρ
      (canonicalSourcePairData_ranges k B V T J j b c s v e f t u i x r gate hX D he hf ρ)
      (le_max_right _ _)

theorem canonicalSourceNormalizedData_degreeCost (k : ℕ) (B V : ℕ → ℤ) (T : ℕ → ℝ)
    (J : ℤ) (j : ℕ) (b c : Bool) (s v : ℤ) (e f : Expressions (ι:=ι) k j)
    (t u : HistoryReconstruction.Tree j) (i : ι) (x : Other i → ℤ) (r : ℤ)
    (gate : Bool) (X Δ Wp Wl H : ℝ) (D M : ℕ) (copy : Expr ι) (Tc Wc : ℝ)
    (he : ∀z,(e z).syntaxSize ≤ M) (hf : ∀z,(f z).syntaxSize ≤ M)
    (hc : copy.syntaxSize ≤ M) :
    (canonicalSourceNormalizedData k B V T J j b c s v e f t u i x r gate
      X Δ Wp Wl H D copy Tc Wc).degreeCost ≤
      (6+2*sourceDegreeFactor k j)*(M+1)+1 := by
  have hmul := multiplyData_degreeCost (ratioExpressionData i x copy Tc (-Wc) Wc)
    (canonicalSourcePairData k B V T J j b c s v e f t u i x r gate X Δ Wp Wl H D)
  have hr := ratioExpressionData_degreeCost i x copy Tc (-Wc) Wc
  have hp := canonicalSourcePairData_degreeCost k B V T J j b c s v e f t u i x r gate
    X Δ Wp Wl H D M he hf
  change (multiplyData _ _).degreeCost ≤ _
  have hlin : (6+2*sourceDegreeFactor k j)*(M+1)+1 =
      6*(M+1)+2*sourceDegreeFactor k j*(M+1)+1 := by ring
  rw [hlin]
  omega

theorem canonicalSourceNormalizedData_weight (k : ℕ) (B V : ℕ → ℤ) (T : ℕ → ℝ)
    (J : ℤ) (j : ℕ) (b c : Bool) (s v : ℤ) (e f : Expressions (ι:=ι) k j)
    (t u : HistoryReconstruction.Tree j) (i : ι) (x : Other i → ℤ) (r : ℤ)
    (gate : Bool) (X Δ Wp Wl H : ℝ) (D : ℕ) (copy : Expr ι) (Tc Wc : ℝ)
    (n : ℤ) (hc : HistoryReconstruction.Good (insertCoordinate i x n) copy)
    (ρ : 𝓢(ℝ,ℂ)) :
    (canonicalSourceNormalizedData k B V T J j b c s v e f t u i x r gate
      X Δ Wp Wl H D copy Tc Wc).weight ρ (n:ℝ) =
    (if Real.exp (Tc-Wc) ≤ (copy.integerEval (insertCoordinate i x n):ℝ) ∧
        (copy.integerEval (insertCoordinate i x n):ℝ) ≤ Real.exp (Tc+Wc)
      then (Real.exp Tc:ℂ)/(copy.integerEval (insertCoordinate i x n):ℂ) else 0) *
      (canonicalSourcePairData k B V T J j b c s v e f t u i x r gate
        X Δ Wp Wl H D).weight ρ (n:ℝ) := by
  rw [canonicalSourceNormalizedData,multiplyData_weight,ratioExpressionData_weight i x copy Tc (-Wc) Wc n hc]
  simp only [neg_neg,Real.exp_sub,Real.exp_add,Real.exp_neg,div_eq_mul_inv]

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
