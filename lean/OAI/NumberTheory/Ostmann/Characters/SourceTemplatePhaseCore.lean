import OAI.NumberTheory.Ostmann.Characters.SourceTemplatePhaseDefs

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Construction Preliminaries Template
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

theorem sourcePullback_otherProduct {k Q:ℕ} (cfg:SourceConfiguration k) (m:ℕ)
    (w:Fin (sourceHalfSize cfg m+sourceHalfSize cfg m)→PrimeUpTo Q)
    (i:SourceConstituent cfg m) :
    otherProduct (fun i => (w (sourceIndexEquiv cfg m i)).val) i =
      otherProduct (fun i => (w i).val) (sourceIndexEquiv cfg m i) :=
  otherProduct_equiv (sourceIndexEquiv cfg m) (fun i => (w i).val) i (primeUpTo_prime _).ne_zero

theorem sourcePullback_crtFrequency {k Q:ℕ} (cfg:SourceConfiguration k) (m:ℕ)
    (w:Fin (sourceHalfSize cfg m+sourceHalfSize cfg m)→PrimeUpTo Q)
    (s:ℤ) (i:SourceConstituent cfg m) :
    crtFrequency (fun i => (w (sourceIndexEquiv cfg m i)).val) s i =
      crtFrequency (fun i => (w i).val) s (sourceIndexEquiv cfg m i) := by
  unfold crtFrequency
  rw [sourcePullback_otherProduct]

theorem sourcePullback_unitHistoryPhase {k Q:ℕ} (cfg:SourceConfiguration k) (m:ℕ)
    (χ:Fin (sourceHalfSize cfg m)→(q:ℕ)→MulChar (ZMod q) ℂ)
    (a:Fin (sourceHalfSize cfg m)→(q:ℕ)→ZMod q)
    (ζ:Fin (sourceHalfSize cfg m)→ℕ→ℂ)
    (w:Fin (sourceHalfSize cfg m+sourceHalfSize cfg m)→PrimeUpTo Q)
    (s:ℤ) (t:HistoryReconstruction.Tree 0) :
    unitHistoryPhase k 0 (sourceWidth cfg m)
      (sourceUnitData cfg m ζ) (sourceCharacterData cfg m χ) (sourceTranslationData cfg m a)
      (fun i => w (sourceIndexEquiv cfg m i)) s t =
      letI : ∀i,Fact (w i).val.Prime := fun i => ⟨primeUpTo_prime (w i)⟩
      (∏i,characterDoublePhase ζ i (w i).val)*
        initialPhase (fun i => (w i).val) (fun i => characterDoubleChar χ i (w i).val)
          (fun i => characterDoubleCenter a i (w i).val) s := by
  let : ∀i,Fact (w i).val.Prime := fun i => ⟨primeUpTo_prime (w i)⟩
  rw [unitHistoryPhase,sampledHistoryPhase_zero]
  unfold sampleUnitMultiplier sourceUnitData sourceCharacterData sourceTranslationData
  rw [(sourceIndexEquiv cfg m).prod_comp (fun i => characterDoublePhase ζ i (w i).val)]
  exact congrArg (fun z:ℂ => (∏i,characterDoublePhase ζ i (w i).val)*z)
    (initialPhase_reindex (sourceIndexEquiv cfg m) (fun i => (w i).val)
      (fun i => characterDoubleChar χ i (w i).val)
      (fun i => characterDoubleCenter a i (w i).val) s)

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
