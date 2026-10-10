import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationProfileBudget
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSurvivingData

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators SchwartzMap FourierTransform
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template TemplateSupportRemoval TemplateOneSidedBudget
open HistoryFrequencyLabels HistoryFrequencyBudget Arithmetic
attribute [local instance] Classical.propDecidable

def survivingProfileSyntax (k j : ℕ) (width : Role → ℕ) (N : ℕ) : ℕ :=
  2*(N+Fintype.card (CopiedConstituent (schedule k j) j width)+1)

theorem survivingProfileSyntax_bounds (k j : ℕ) (width : Role → ℕ)
    (N : ℕ) (hw : ∀q,width q ≤ N) (P : ℤ)
    (σ : Equiv.Perm (CopiedConstituent (schedule k j) j width)) :
    (∀i,(survivingSampledExpressions k j width P σ i).syntaxSize ≤
      survivingProfileSyntax k j width N) ∧
    (survivingCopiedProductExpression k j width).syntaxSize ≤
      survivingProfileSyntax k j width N := by
  constructor
  · intro i
    exact (survivingSampledExpressions_syntaxSize k j width P σ N hw i).trans (by
      unfold survivingProfileSyntax
      omega)
  · exact (survivingCopiedProductExpression_syntaxSize k j width).trans (by
      unfold survivingProfileSyntax
      omega)

theorem survivingNormalizedData_ranges_degree (k j : ℕ) (width : Role → ℕ)
    (B V : ℕ → ℤ) (T : ℕ → ℝ) (J P s v : ℤ)
    (σ π : Equiv.Perm (CopiedConstituent (schedule k j) j width))
    (t u : HistoryReconstruction.Tree j) (i : SurvivingPrimeIndex k j width)
    (x : Other i → ℤ) (r : ℤ) (gate : Bool)
    {X Δ Wp Wl H Tc Wc : ℝ} (hX : 0 < X) (hWc : 0 ≤ Wc)
    (N : ℕ) (hw : ∀q,width q ≤ N) (ρ : 𝓢(ℝ,ℂ)) :
    let D := obstructionSizeFactor k j*(2*(N+1)+1)
    let data := canonicalSourceNormalizedData k B V T J j false true s v
      (survivingSampledExpressions k j width P σ)
      (survivingSampledExpressions k j width P π) t u i x r gate
      X Δ Wp Wl H D (survivingCopiedProductExpression k j width) Tc Wc
    data.Ranges ρ
      (Sum.elim (fun _=>-Wc) (fun _=>coarseLower D H Δ Wl))
      (Sum.elim (fun _=>Wc) (fun _=>-Δ+Wl))
      (max (Real.exp Wc) (Real.exp ((-Δ+Wl)/2)*leafProfileBound ρ)) ∧
    data.degreeCost ≤ (6+2*sourceDegreeFactor k j)*
      (survivingProfileSyntax k j width N+1)+1 := by
  dsimp only
  constructor
  · apply canonicalSourceNormalizedData_ranges k B V T J j false true s v
      (survivingSampledExpressions k j width P σ)
      (survivingSampledExpressions k j width P π) t u i x r gate hX _
      (survivingCopiedProductExpression k j width) Tc Wc hWc
    · exact (survivingCopiedProductExpression_good k j width (fun _=>0)).1
    · exact survivingSampledExpressions_good k j width P σ
    · exact survivingSampledExpressions_good k j width P π
  · exact canonicalSourceNormalizedData_degreeCost k B V T J j false true s v
      (survivingSampledExpressions k j width P σ)
      (survivingSampledExpressions k j width P π) t u i x r gate X Δ Wp Wl H _ _
      (survivingCopiedProductExpression k j width) Tc Wc
      (survivingProfileSyntax_bounds k j width N hw P σ).1
      (survivingProfileSyntax_bounds k j width N hw P π).1
      (survivingProfileSyntax_bounds k j width N hw P σ).2

theorem survivingProfile_linear_budgets (k j : ℕ) (width : Role → ℕ)
    (N m Cw Cc : ℕ) (hN : N ≤ Cw*(m+1))
    (hc : Fintype.card (CopiedConstituent (schedule k j) j width) ≤ Cc*(m+1)) :
    (obstructionSizeFactor k j*(2*(N+1)+1):ℝ) ≤
      (obstructionSizeFactor k j*(2*Cw+3):ℕ)*(1+(m:ℝ)) ∧
    (survivingProfileSyntax k j width N:ℝ) ≤
      (2*(Cw+Cc+1):ℕ)*(1+(m:ℝ)) := by
  have hD : obstructionSizeFactor k j*(2*(N+1)+1) ≤
      (obstructionSizeFactor k j*(2*Cw+3))*(m+1) := by
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    nlinarith
  have hM : survivingProfileSyntax k j width N ≤ (2*(Cw+Cc+1))*(m+1) := by
    unfold survivingProfileSyntax
    nlinarith
  constructor
  · have hh := (show ((obstructionSizeFactor k j*(2*(N+1)+1):ℕ):ℝ) ≤
      (((obstructionSizeFactor k j*(2*Cw+3))*(m+1):ℕ):ℝ) from by exact_mod_cast hD)
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,add_comm (m:ℝ) 1] using hh
  · have hh := (show (survivingProfileSyntax k j width N:ℝ) ≤
      (((2*(Cw+Cc+1))*(m+1):ℕ):ℝ) from by exact_mod_cast hM)
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,add_comm (m:ℝ) 1] using hh

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
