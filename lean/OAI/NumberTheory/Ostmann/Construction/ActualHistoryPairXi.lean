import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSmoothXi
import OAI.NumberTheory.Ostmann.Construction.ActualHistoryPairExpansion

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate FourierTransform Classical
namespace Ostmann.Construction
open Arithmetic HistoryPairPattern HistoryPairSmoothXi

def supportedHistoryPairXi (d : Decomposition) (V : ℕ→ℕ) (outside : List ℕ)
    (b s : ℕ) (X tb td G : ℝ) {l : ℕ} (h k : History l) : ℂ :=
  if hs : h.Supported V outside then
    if ks : k.Supported V outside then
      ((h.compensationProduct:ℂ)*(k.compensationProduct:ℂ))*
        pairedRealXi b s X tb td G h k hs ks (fun i => (pairSample h k i:ℝ))*
        (h.leafProduct (spectatorFactor (residueTransform d) outside)*
          conj (k.leafProduct (spectatorFactor (residueTransform d) outside)))
    else 0
  else 0

theorem supportedWeight_pair_eq_Xi (d : Decomposition) (V : ℕ→ℕ) (outside : List ℕ)
    (b s : ℕ) (X tb td G : ℝ) {l : ℕ} (h k : History l)
    (hroot : RootGiantsAgree h k) :
    h.supportedWeight V outside
        (baseCoefficient X (fun ξ => 𝓕 SchwartzCutoff.psi ξ) (residueTransform d)
          (sourceStateBins b s tb td) outside) Ostmann.smoothPartition G *
      conj (k.supportedWeight V outside
        (baseCoefficient X (fun ξ => 𝓕 SchwartzCutoff.psi ξ) (residueTransform d)
          (sourceStateBins b s tb td) outside) Ostmann.smoothPartition G)=
    supportedHistoryPairXi d V outside b s X tb td G h k := by
  by_cases hs : h.Supported V outside
  · by_cases ks : k.Supported V outside
    · simp only [History.supportedWeight,hs,ks,ite_true,supportedHistoryPairXi,dite_eq_left]
      rw [pairedRealXi_integer_sample b s X tb td G h k hs ks hroot]
      exact history_pair_compensation_factor X G (residueTransform d)
        (sourceStateBins b s tb td) outside h k
    · simp [History.supportedWeight,supportedHistoryPairXi,hs,ks]
  · simp [History.supportedWeight,supportedHistoryPairXi,hs]

theorem decoded_counterpart_rootGiantsAgree (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (giant : PrimeSource) (l p : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (x : RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant)
    (v : ℤ) (e : Equiv.Perm (RemainingIndex (Template.remainder (l+1) (Template.current seed l))))
    (he : CounterpartCompatible sources (Template.remainder (l+1) (Template.current seed l)) giant x e)
    (hb : PreservesRemainingBands (Template.remainder (l+1) (Template.current seed l)) e)
    (c₁ c₂ : HistoryChoices sources seed V l) :
    RootGiantsAgree
      (decodeHistory sources seed V l (remainingState sources (Template.current seed l) (l+1) giant p u x v) c₁)
      (decodeHistory sources seed V l (remainingState sources (Template.current seed l) (l+1) giant p u
        (reconstructCounterpart sources (Template.remainder (l+1) (Template.current seed l)) giant x e he) v) c₂) := by
  unfold RootGiantsAgree
  simp only [decodeHistory_root,remainingState]
  constructor
  · trivial
  · simp only [reconstructCounterpart,hb.fixes_giant,remainingCoordinate,Fin.cases_zero]

end Ostmann.Construction

end

end OAI
