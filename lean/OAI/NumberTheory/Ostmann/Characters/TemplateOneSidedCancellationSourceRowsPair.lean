import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSourceRowsWeight

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template TemplateSupportRemoval
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [DecidableEq ι]

def historyPairResidueModulus (k j : ℕ) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (s' : ℤ) (e' : Expressions (ι:=ι) k j)
    (t' : HistoryReconstruction.Tree j) : ℕ :=
  pairResidueModulus (historyResidueGuards k j s e t) (historyResidueGuards k j s' e' t')

omit [DecidableEq ι] in
theorem historyPairResidueModulus_pos (k : ℕ) (V : ℕ → ℤ) (j : ℕ)
    (s : ℤ) (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j)
    (s' : ℤ) (e' : Expressions (ι:=ι) k j) (t' : HistoryReconstruction.Tree j)
    (hf : historyFrequencyBounds V j s t) (hf' : historyFrequencyBounds V j s' t')
    (he : ∀u,(e u).Valid) (he' : ∀u,(e' u).Valid) :
    0 < historyPairResidueModulus k j s e t s' e' t' :=
  pairResidueModulus_pos _ _ (historyResidueGuards_valid k V j s e t he hf)
    (historyResidueGuards_valid k V j s' e' t' he' hf')

omit [DecidableEq ι] in
theorem historyPairResidueModulus_divisibility (k j : ℕ)
    (s : ℤ) (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j)
    (s' : ℤ) (e' : Expressions (ι:=ι) k j) (t' : HistoryReconstruction.Tree j) :
    residueModulus (historyResidueGuards k j s e t) ∣
        (historyPairResidueModulus k j s e t s' e' t':ℤ) ∧
      residueModulus (historyResidueGuards k j s' e' t') ∣
        (historyPairResidueModulus k j s e t s' e' t':ℤ) :=
  ⟨residueModulus_dvd_pair_left _ _,residueModulus_dvd_pair_right _ _⟩

theorem frequencyArithmetic_pair_progression (k : ℕ) (V : ℕ → ℤ) (j : ℕ)
    (s : ℤ) (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j)
    (s' : ℤ) (e' : Expressions (ι:=ι) k j) (t' : HistoryReconstruction.Tree j)
    (hf : historyFrequencyBounds V j s t) (hf' : historyFrequencyBounds V j s' t')
    (he : ∀a u,HistoryReconstruction.Good a (e u))
    (he' : ∀a u,HistoryReconstruction.Good a (e' u))
    (i : ι) (x : Other i → ℤ) (r n : ℤ) :
    let Q := historyPairResidueModulus k j s e t s' e' t'
    (frequencyArithmetic k V j s (evalExpressions (insertCoordinate i x ((Q:ℤ)*n+r)) e) t ∧
      frequencyArithmetic k V j s' (evalExpressions (insertCoordinate i x ((Q:ℤ)*n+r)) e') t') ↔
    (frequencyArithmetic k V j s (evalExpressions (insertCoordinate i x r) e) t ∧
      frequencyArithmetic k V j s' (evalExpressions (insertCoordinate i x r) e') t') := by
  dsimp only
  have hd := historyPairResidueModulus_divisibility k j s e t s' e' t'
  exact and_congr
    (frequencyArithmetic_progression_of_dvd k V j s e t hf he _ hd.1 i x r n)
    (frequencyArithmetic_progression_of_dvd k V j s' e' t' hf' he' _ hd.2 i x r n)

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
