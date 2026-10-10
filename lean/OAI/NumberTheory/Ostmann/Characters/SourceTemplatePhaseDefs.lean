import OAI.NumberTheory.Ostmann.Characters.SourceTemplateIndices
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceUnitAmplitude
import OAI.NumberTheory.Ostmann.Characters.TemplateInitialPhaseReindex

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Construction Preliminaries Template
open scoped BigOperators ComplexConjugate

def sourceCharacterData {k Q:ℕ} (cfg:SourceConfiguration k) (m:ℕ)
    (χ:Fin (sourceHalfSize cfg m)→(q:ℕ)→MulChar (ZMod q) ℂ) :
    PrimeCharacterData (schedule k 0) (sourceWidth cfg m) Q :=
  fun i p => characterDoubleChar χ (sourceIndexEquiv cfg m i) p.val

def sourceTranslationData {k Q:ℕ} (cfg:SourceConfiguration k) (m:ℕ)
    (a:Fin (sourceHalfSize cfg m)→(q:ℕ)→ZMod q) :
    PrimeTranslationData (schedule k 0) (sourceWidth cfg m) Q :=
  fun i p => characterDoubleCenter a (sourceIndexEquiv cfg m i) p.val

def sourceUnitData {k Q:ℕ} (cfg:SourceConfiguration k) (m:ℕ)
    (ζ:Fin (sourceHalfSize cfg m)→ℕ→ℂ) :
    PrimeUnitData (schedule k 0) (sourceWidth cfg m) Q :=
  fun i p => characterDoublePhase ζ (sourceIndexEquiv cfg m i) p.val

theorem norm_sourceUnitData {k Q:ℕ} (cfg:SourceConfiguration k) (m:ℕ)
    (ζ:Fin (sourceHalfSize cfg m)→ℕ→ℂ)
    (hζ:∀i (p:PrimeUpTo Q),‖ζ i p.val‖=1) (i:SourceConstituent cfg m) (p:PrimeUpTo Q) :
    ‖sourceUnitData cfg m ζ i p‖=1 := by
  unfold sourceUnitData
  refine Fin.addCases (fun z => ?_) (fun z => ?_) (sourceIndexEquiv cfg m i)
  · simpa only [characterDoublePhase,Fin.append_left] using hζ z p
  · simpa only [characterDoublePhase,Fin.append_right,Complex.norm_conj] using hζ z p

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
