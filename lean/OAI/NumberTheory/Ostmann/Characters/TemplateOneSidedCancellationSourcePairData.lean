import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSourceBudgetSplitWidth
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSourceRowsSplitWidthWeight

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators SchwartzMap FourierTransform
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template TemplateSupportRemoval Arithmetic HigherBiasSource.SourceTemplate
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [DecidableEq ι]

def canonicalSourcePairData (k : ℕ) (B V : ℕ → ℤ) (T : ℕ → ℝ)
    (J : ℤ) (j : ℕ) (b c : Bool) (s v : ℤ) (e f : Expressions (ι:=ι) k j)
    (t u : HistoryReconstruction.Tree j) (i : ι) (x : Other i → ℤ) (r : ℤ)
    (gate : Bool) (X Δ Wp Wl H : ℝ) (D : ℕ) :=
  gatedData gate (multiplyData
    (canonicalSourceRowDataSplitWidth k B V T J j b s e t i x r X Δ Wp Wl H D)
    (canonicalSourceRowDataSplitWidth k B V T J j c v f u i x r X Δ Wp Wl H D))

theorem canonicalSourcePairData_ranges (k : ℕ) (B V : ℕ → ℤ) (T : ℕ → ℝ)
    (J : ℤ) (j : ℕ) (b c : Bool) (s v : ℤ) (e f : Expressions (ι:=ι) k j)
    (t u : HistoryReconstruction.Tree j) (i : ι) (x : Other i → ℤ) (r : ℤ)
    (gate : Bool) {X Δ Wp Wl H : ℝ} (hX : 0 < X) (D : ℕ)
    (he : ∀a z,HistoryReconstruction.Good a (e z))
    (hf : ∀a z,HistoryReconstruction.Good a (f z)) (ρ : 𝓢(ℝ,ℂ)) :
    (canonicalSourcePairData k B V T J j b c s v e f t u i x r gate X Δ Wp Wl H D).Ranges ρ
      (fun _=>coarseLower D H Δ Wl) (fun _=>-Δ+Wl)
      (Real.exp ((-Δ+Wl)/2)*leafProfileBound ρ) := by
  apply gatedData_ranges
  convert multiplyData_ranges _ _ ρ
    (canonicalSourceRowDataSplitWidth_ranges k B V T J j b s e t i x r
      (Δ:=Δ) (Wp:=Wp) (Wl:=Wl) (H:=H) hX D (he _) ρ)
    (canonicalSourceRowDataSplitWidth_ranges k B V T J j c v f u i x r
      (Δ:=Δ) (Wp:=Wp) (Wl:=Wl) (H:=H) hX D (hf _) ρ) using 1 <;>
    ext z <;> cases z <;> rfl

theorem canonicalSourcePairData_degreeCost (k : ℕ) (B V : ℕ → ℤ) (T : ℕ → ℝ)
    (J : ℤ) (j : ℕ) (b c : Bool) (s v : ℤ) (e f : Expressions (ι:=ι) k j)
    (t u : HistoryReconstruction.Tree j) (i : ι) (x : Other i → ℤ) (r : ℤ)
    (gate : Bool) (X Δ Wp Wl H : ℝ) (D M : ℕ)
    (he : ∀z,(e z).syntaxSize ≤ M) (hf : ∀z,(f z).syntaxSize ≤ M) :
    (canonicalSourcePairData k B V T J j b c s v e f t u i x r gate X Δ Wp Wl H D).degreeCost ≤
      2*sourceDegreeFactor k j*(M+1)+1 := by
  have hp := multiplyData_degreeCost
    (canonicalSourceRowDataSplitWidth k B V T J j b s e t i x r X Δ Wp Wl H D)
    (canonicalSourceRowDataSplitWidth k B V T J j c v f u i x r X Δ Wp Wl H D)
  rw [canonicalSourceRowDataSplitWidth_degreeCost,
    canonicalSourceRowDataSplitWidth_degreeCost] at hp
  have hl := canonicalSourceLeafDataSplitWidth_degreeCost k B V T J j b s e t i x X Δ Wp Wl H D M he
  have hr := canonicalSourceLeafDataSplitWidth_degreeCost k B V T J j c v f u i x X Δ Wp Wl H D M hf
  rw [canonicalSourcePairData,gatedData_degreeCost]
  have hi : 2*sourceDegreeFactor k j*(M+1)=2*(sourceDegreeFactor k j*(M+1)) := by ring
  rw [hi]
  omega

theorem canonicalSourcePairData_weight_nat (k : ℕ) (B V : ℕ → ℤ) (T : ℕ → ℝ)
    (J : ℤ) (j : ℕ) (b c : Bool) (s v : ℤ) (e f : Expressions (ι:=ι) k j)
    (t u : HistoryReconstruction.Tree j) (i : ι) (x : Other i → ℤ)
    (gate : Bool) (Q r n : ℕ)
    (ht : historyFrequencyBounds V j s t) (hu : historyFrequencyBounds V j v u)
    (he : ∀a z,HistoryReconstruction.Good a (e z))
    (hf : ∀a z,HistoryReconstruction.Good a (f z))
    (hQt : residueModulus (historyResidueGuards k j s e t) ∣ (Q:ℤ))
    (hQu : residueModulus (historyResidueGuards k j v f u) ∣ (Q:ℤ))
    {X Δ Wp Wl H : ℝ} (hX : 1 ≤ X) (hH : Real.log 2 ≤ H) (D : ℕ)
    (hst : ∀ z : Fin (2^j),(periodExpression k (indexedBottomExpressions k j b s e t z).2.2).syntaxSize ≤ D)
    (hsu : ∀ z : Fin (2^j),(periodExpression k (indexedBottomExpressions k j c v f u z).2.2).syntaxSize ≤ D)
    (hft : ∀ z : Fin (2^j),(periodExpression k (indexedBottomExpressions k j b s e t z).2.2).FixedLogBound H)
    (hfu : ∀ z : Fin (2^j),(periodExpression k (indexedBottomExpressions k j c v f u z).2.2).FixedLogBound H)
    (hvars : ∀z,|((insertCoordinate i x ((Q*n+r:ℕ):ℤ) z : ℤ) : ℝ)| ≤ Real.exp H) :
    (canonicalSourcePairData k B V T J j b c s v e f t u i x (r:ℤ) gate X Δ Wp Wl H D).weight
      (𝓕 SchwartzCutoff.psi) ((Q*n+r:ℕ):ℝ) =
    if gate then
      conjugateBy b (coreHistoryWeight k (fun l _=>B l) (fun l _=>V l)
        (canonicalHistoryExtra k (fun l=>pivotWindow (T l) Wp))
        (canonicalHistoryMask k (sourceRangeLeafMask k J X Δ Wl))
        X Δ Wl j s (evalExpressions (insertCoordinate i x ((Q*n+r:ℕ):ℤ)) e) t) *
      conjugateBy c (coreHistoryWeight k (fun l _=>B l) (fun l _=>V l)
        (canonicalHistoryExtra k (fun l=>pivotWindow (T l) Wp))
        (canonicalHistoryMask k (sourceRangeLeafMask k J X Δ Wl))
        X Δ Wl j v (evalExpressions (insertCoordinate i x ((Q*n+r:ℕ):ℤ)) f) u)
    else 0 := by
  rw [canonicalSourcePairData,gatedData_weight,multiplyData_weight,
    canonicalSourceRowDataSplitWidth_weight_nat k B V T J j b s e t i x Q r n ht he hQt hX hH D hst hft hvars,
    canonicalSourceRowDataSplitWidth_weight_nat k B V T J j c v f u i x Q r n hu hf hQu hX hH D hsu hfu hvars]

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
