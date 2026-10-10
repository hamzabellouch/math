import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedBudgetFrequency
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSourcePairData
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSourceRowsPair

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators SchwartzMap FourierTransform
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template TemplateSupportRemoval TemplateOneSidedBudget
open HistoryFrequencyLabels HistoryFrequencyBudget HigherBiasSource.SourceTemplate
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
theorem actual_indexed_period_parameters {a m H : ℝ} (k j : ℕ) (ha : 0 ≤ a) (hm : 1 ≤ m)
    (hH : Real.log 2 ≤ H) (hfreq : linearEnvelope a j*m ≤ H)
    (b : Bool) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (ht : RangeSupported (ranges a m j) j [] s t)
    (M : ℕ) (he : ∀z,(e z).syntaxSize ≤ M) (hfixed : ∀z,(e z).FixedLogBound H) :
    (∀z : Fin (2^j),(periodExpression k (indexedBottomExpressions k j b s e t z).2.2).syntaxSize ≤
      obstructionSizeFactor k j*(M+1)) ∧
    (∀z : Fin (2^j),(periodExpression k (indexedBottomExpressions k j b s e t z).2.2).FixedLogBound H) := by
  have hH0 : 0 ≤ H := (Real.log_nonneg (by norm_num : (1:ℝ)≤2)).trans hH
  have hB : 1 ≤ Real.exp H := Real.one_le_exp_iff.mpr hH0
  have hmem (z : Fin (2^j)) :
      periodExpression k (indexedBottomExpressions k j b s e t z).2.2 ∈
        obstructionExpressions k j b s e t :=
    List.mem_append_right _ (List.mem_map.mpr
      ⟨_,indexedBottomExpressions_mem k j b s e t z,rfl⟩)
  refine ⟨fun z=>obstructionExpressions_size k j b s e t M he _ (hmem z),?_⟩
  intro z
  exact obstructionExpressions_fixedBound k j (ranges a m j) hB
    (fun p v hv => (actual_frequency_abs_le_exp ha hm j p v hv).trans
      (Real.exp_le_exp.mpr hfreq)) [] b s e t hfixed ht _ (hmem z)

theorem canonicalSourcePairData_weight_actual {a m H : ℝ} (ha : 0 ≤ a) (hm : 1 ≤ m)
    (k j : ℕ) (B : ℕ → ℤ) (T : ℕ → ℝ) (J : ℤ)
    (b c : Bool) (s v : ℤ) (e f : Expressions (ι:=ι) k j)
    (t u : HistoryReconstruction.Tree j)
    (ht : RangeSupported (ranges a m j) j [] s t)
    (hu : RangeSupported (ranges a m j) j [] v u)
    (i : ι) (x : Other i → ℤ) (gate : Bool) (r n : ℕ)
    (he : ∀y z,HistoryReconstruction.Good y (e z))
    (hf : ∀y z,HistoryReconstruction.Good y (f z))
    {X Δ Wp Wl : ℝ} (hX : 1 ≤ X) (hH : Real.log 2 ≤ H)
    (hfreq : linearEnvelope a j*m ≤ H) (M : ℕ)
    (het : ∀z,(e z).syntaxSize ≤ M) (hfu : ∀z,(f z).syntaxSize ≤ M)
    (hef : ∀z,(e z).FixedLogBound H) (hff : ∀z,(f z).FixedLogBound H)
    (hvars : ∀z,|((insertCoordinate i x
      ((historyPairResidueModulus k j s e t v f u*n+r:ℕ):ℤ) z : ℤ) : ℝ)| ≤ Real.exp H) :
    let Q := historyPairResidueModulus k j s e t v f u
    let D := obstructionSizeFactor k j*(M+1)
    (canonicalSourcePairData k B (fun l=>(bound a m l:ℤ)) T J j b c s v e f t u i x (r:ℤ)
      gate X Δ Wp Wl H D).weight (𝓕 SchwartzCutoff.psi) ((Q*n+r:ℕ):ℝ) =
    if gate then
      conjugateBy b (coreHistoryWeight k (fun l _=>B l) (fun l _=>(bound a m l:ℤ))
        (canonicalHistoryExtra k (fun l=>pivotWindow (T l) Wp))
        (canonicalHistoryMask k (sourceRangeLeafMask k J X Δ Wl))
        X Δ Wl j s (evalExpressions (insertCoordinate i x ((Q*n+r:ℕ):ℤ)) e) t) *
      conjugateBy c (coreHistoryWeight k (fun l _=>B l) (fun l _=>(bound a m l:ℤ))
        (canonicalHistoryExtra k (fun l=>pivotWindow (T l) Wp))
        (canonicalHistoryMask k (sourceRangeLeafMask k J X Δ Wl))
        X Δ Wl j v (evalExpressions (insertCoordinate i x ((Q*n+r:ℕ):ℤ)) f) u)
    else 0 := by
  dsimp only
  have htp := actual_indexed_period_parameters k j ha hm hH hfreq b s e t ht M het hef
  have hup := actual_indexed_period_parameters k j ha hm hH hfreq c v f u hu M hfu hff
  have hQ := historyPairResidueModulus_divisibility k j s e t v f u
  exact canonicalSourcePairData_weight_nat k B _ T J j b c s v e f t u i x gate _ r n
    (actual_historyFrequencyBounds a m j j [] (by simp) s t ht)
    (actual_historyFrequencyBounds a m j j [] (by simp) v u hu)
    he hf hQ.1 hQ.2 hX hH _ htp.1 hup.1 htp.2 hup.2 hvars

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
