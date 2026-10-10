import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationEmptyData
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSourceData
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSourceRowsBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators SchwartzMap FourierTransform
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template TemplateSupportRemoval Arithmetic HigherBiasSource.SourceTemplate
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [DecidableEq ι]

def canonicalSourceRowData (k : ℕ) (B V : ℕ → ℤ) (T : ℕ → ℝ)
    (J : ℤ) (j : ℕ) (b : Bool) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (i : ι) (x : Other i → ℤ) (r : ℤ)
    (X Δ W H : ℝ) (D : ℕ) :
    HistoryPolynomialData
      (Option (Fin (canonicalSourceGuardList k B V T J X Δ W j s e t).length
        ⊕ (Fin (2^j) × Bool))) (Fin (2^j)) :=
  gatedData (decide (frequencyArithmetic k V j s (evalExpressions (insertCoordinate i x r) e) t))
    (canonicalSourceLeafData k B V T J j b s e t i x X Δ W H D)

theorem canonicalSourceRowData_ranges (k : ℕ) (B V : ℕ → ℤ) (T : ℕ → ℝ)
    (J : ℤ) (j : ℕ) (b : Bool) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (i : ι) (x : Other i → ℤ) (r : ℤ)
    {X Δ W H : ℝ} (hX : 0 < X) (D : ℕ)
    (he : ∀u,HistoryReconstruction.Good (insertCoordinate i x r) (e u))
    (ρ : 𝓢(ℝ,ℂ)) :
    (canonicalSourceRowData k B V T J j b s e t i x r X Δ W H D).Ranges ρ
      (fun _ => coarseLower D H Δ W) (fun _ => -Δ+W)
      (Real.exp ((-Δ+W)/2)*leafProfileBound ρ) := by
  unfold canonicalSourceRowData
  by_cases hf : frequencyArithmetic k V j s (evalExpressions (insertCoordinate i x r) e) t
  · apply gatedData_ranges
    exact canonicalSourceLeafData_ranges k B V T J j b s e t i x _ hX D he hf ρ
  · simp only [hf,decide_false]
    apply gatedData_false_ranges
    · exact mul_nonneg (Real.exp_pos _).le (leafProfileBound_pos ρ).le
    · exact fun _ => min_le_right _ _
    · exact fun _ => hX
    · exact fun _ => le_rfl

theorem canonicalSourceRowData_degreeCost (k : ℕ) (B V : ℕ → ℤ) (T : ℕ → ℝ)
    (J : ℤ) (j : ℕ) (b : Bool) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (i : ι) (x : Other i → ℤ) (r : ℤ)
    (X Δ W H : ℝ) (D : ℕ) :
    (canonicalSourceRowData k B V T J j b s e t i x r X Δ W H D).degreeCost =
      (canonicalSourceLeafData k B V T J j b s e t i x X Δ W H D).degreeCost :=
  gatedData_degreeCost _ _

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
