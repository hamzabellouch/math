import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationCoreData
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCanonicalGuardsGood

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators SchwartzMap FourierTransform
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template TemplateSupportRemoval Arithmetic HigherBiasSource.SourceTemplate
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [DecidableEq ι]

def canonicalSourceLeafData (k : ℕ) (B V : ℕ → ℤ) (T : ℕ → ℝ)
    (J : ℤ) (j : ℕ) (b : Bool) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (i : ι) (x : Other i → ℤ)
    (X Δ W H : ℝ) (D : ℕ) :
    HistoryPolynomialData
      (Fin (canonicalSourceGuardList k B V T J X Δ W j s e t).length ⊕ (Fin (2^j) × Bool))
      (Fin (2^j)) :=
  leafData k (fun q => (canonicalSourceGuardList k B V T J X Δ W j s e t).get q)
    (indexedBottomExpressions k j b s e t) i x X (coarseLower D H Δ W) (-Δ+W)

theorem canonicalSourceLeafData_weight (k : ℕ) (B V : ℕ → ℤ) (T : ℕ → ℝ)
    (J : ℤ) (j : ℕ) (b : Bool) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (i : ι) (x : Other i → ℤ) (n : ℤ)
    {X Δ W H : ℝ} (hX : 1 ≤ X) (hH : Real.log 2 ≤ H) (D : ℕ)
    (he : ∀u,HistoryReconstruction.Good (insertCoordinate i x n) (e u))
    (hs : ∀ u : Fin (2^j),(periodExpression k (indexedBottomExpressions k j b s e t u).2.2).syntaxSize ≤ D)
    (hfixed : ∀ u : Fin (2^j),(periodExpression k (indexedBottomExpressions k j b s e t u).2.2).FixedLogBound H)
    (hvars : ∀u,|((insertCoordinate i x n u : ℤ) : ℝ)| ≤ Real.exp H)
    (hf : frequencyArithmetic k V j s (evalExpressions (insertCoordinate i x n) e) t) :
    (canonicalSourceLeafData k B V T J j b s e t i x X Δ W H D).weight
      (𝓕 SchwartzCutoff.psi) (n:ℝ) =
      conjugateBy b (coreHistoryWeight k (fun l _ => B l) (fun l _ => V l)
        (canonicalHistoryExtra k (fun l => pivotWindow (T l) W))
        (canonicalHistoryMask k (sourceRangeLeafMask k J X Δ W))
        X Δ W j s (evalExpressions (insertCoordinate i x n) e) t) := by
  have hx : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hgood := indexedBottomExpressions_period_good_of_frequencyArithmetic k V j b s e t _ he hf
  have hupper (u : Fin (2^j)) :
      (period k 0 (evalBottom k (insertCoordinate i x n) (indexedBottomExpressions k j b s e t u)).2.2:ℝ) ≤
        X*Real.exp (-coarseLower D H Δ W) := by
    apply (period_upper_from_syntax k _ _ hX hH D (hs u) (hfixed u) hvars (hgood u)).trans
    apply mul_le_mul_of_nonneg_left _ hx.le
    apply Real.exp_le_exp.mpr
    have hh := min_le_left (-(D:ℝ)*H) (-Δ+W)
    dsimp only [coarseLower]
    linarith
  have hg' := canonicalSourceGuardList_good k B V T J X Δ W j s e t _ he hf
  rw [canonicalSourceLeafData,leafData_weight_eq_original_lower k _ _ i x n hx
    (fun u => hg' _ (List.get_mem _ u)) hgood hupper,
    canonicalSourceCoreWeight_eq_profiles k B V T J X Δ W hx j b s e t _]
  simp only [hf,true_and,guardsHold,List.forall_mem_iff_get]
  split_ifs <;> rfl

theorem canonicalSourceLeafData_ranges (k : ℕ) (B V : ℕ → ℤ) (T : ℕ → ℝ)
    (J : ℤ) (j : ℕ) (b : Bool) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (i : ι) (x : Other i → ℤ)
    (a : ι → ℤ) {X Δ W H : ℝ} (hX : 0 < X) (D : ℕ)
    (he : ∀u,HistoryReconstruction.Good a (e u))
    (hf : frequencyArithmetic k V j s (evalExpressions a e) t) (ρ : 𝓢(ℝ,ℂ)) :
    (canonicalSourceLeafData k B V T J j b s e t i x X Δ W H D).Ranges ρ
      (fun _ => coarseLower D H Δ W) (fun _ => -Δ+W)
      (Real.exp ((-Δ+W)/2)*leafProfileBound ρ) := by
  have hguards := canonicalSourceGuardList_good k B V T J X Δ W j s e t a he hf
  have hperiods := indexedBottomExpressions_period_good_of_frequencyArithmetic
    k V j b s e t a he hf
  exact leafData_ranges k _ _ i x hX (min_le_right _ _)
    (fun u => (hguards _ (List.get_mem _ u)).1) (fun u => (hperiods u).1) ρ

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
