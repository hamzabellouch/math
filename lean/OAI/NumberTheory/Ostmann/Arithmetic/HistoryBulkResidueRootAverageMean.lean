import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkResidueRootAverageBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkResidueRootAverage
open Construction ResidueHaar HistoryBulkResidueNormSum
open HistoryBulkSpectatorProduct HistoryFrequencyResidues HistoryCRTIntegration
open HistoryBulkDiagramFrequencyAverage

variable (d : Decomposition) {l m : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
  (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
  (hp : ∀q∈outside,q.Prime) (hV : ∀q∈outside,∀j≤l,V j<q)
  (σ : Equiv.Perm (Fin (2^l)×Fin m)) (K : ℕ)

theorem average_canonicalUnit_eq_coupledAverage :
    letI : NeZero outside.prod := HistorySignedSpectatorDiagramAverage.outsideNeZero hp
    letI : NeZero (pairedFrequencyProduct h k) := ⟨pairedFrequencyProduct_ne_zero hs ks⟩
    average (canonicalUnit d h k hs ks hp hV σ K)=
      coupledAverage outside.prod ((pairedFrequencyProduct h k)^(K+2))
        (unitTest h k hs ks hp hV σ (residueTransform d))
        (fun z : UnitPair ((pairedFrequencyProduct h k)^(K+2))=>canonicalRTest (m:=m) K h k (z.1,z.2)) := by
  let : NeZero outside.prod := HistorySignedSpectatorDiagramAverage.outsideNeZero hp
  let : NeZero (pairedFrequencyProduct h k) := ⟨pairedFrequencyProduct_ne_zero hs ks⟩
  exact (coupledAverage_eq_nested
    (unitTest h k hs ks hp hV σ (residueTransform d))
    (fun z : UnitPair ((pairedFrequencyProduct h k)^(K+2))=>canonicalRTest (m:=m) K h k (z.1,z.2))).symm

theorem average_canonicalMixed_eq_coupledAverage :
    letI : NeZero outside.prod := HistorySignedSpectatorDiagramAverage.outsideNeZero hp
    letI : NeZero (pairedFrequencyProduct h k) := ⟨pairedFrequencyProduct_ne_zero hs ks⟩
    average (canonicalMixed d h k hs ks hp hV σ K)=
      coupledAverage outside.prod ((pairedFrequencyProduct h k)^(K+2))
        (mixedTest h k hs ks hp hV σ (residueTransform d))
        (fun z : MixedPair ((pairedFrequencyProduct h k)^(K+2))=>canonicalRTest (m:=m) K h k (z.1,z.2)) := by
  let : NeZero outside.prod := HistorySignedSpectatorDiagramAverage.outsideNeZero hp
  let : NeZero (pairedFrequencyProduct h k) := ⟨pairedFrequencyProduct_ne_zero hs ks⟩
  exact (coupledAverage_eq_nested
    (mixedTest h k hs ks hp hV σ (residueTransform d))
    (fun z : MixedPair ((pairedFrequencyProduct h k)^(K+2))=>canonicalRTest (m:=m) K h k (z.1,z.2))).symm

theorem average_independentUnit_eq_coupledAverage :
    letI : NeZero outside.prod := HistorySignedSpectatorDiagramAverage.outsideNeZero hp
    letI : NeZero (pairedFrequencyProduct h k) := ⟨pairedFrequencyProduct_ne_zero hs ks⟩
    average (independentUnit d h k hs ks hp hV σ K)=
      coupledAverage outside.prod ((pairedFrequencyProduct h k)^(K+2))
        (unitTest h k hs ks hp hV σ (residueTransform d))
        (fun z : UnitPair ((pairedFrequencyProduct h k)^(K+2))=>independentRTest K h k σ (z.1,z.2)) := by
  let : NeZero outside.prod := HistorySignedSpectatorDiagramAverage.outsideNeZero hp
  let : NeZero (pairedFrequencyProduct h k) := ⟨pairedFrequencyProduct_ne_zero hs ks⟩
  exact (coupledAverage_eq_nested
    (unitTest h k hs ks hp hV σ (residueTransform d))
    (fun z : UnitPair ((pairedFrequencyProduct h k)^(K+2))=>independentRTest K h k σ (z.1,z.2))).symm

theorem average_independentMixed_eq_coupledAverage :
    letI : NeZero outside.prod := HistorySignedSpectatorDiagramAverage.outsideNeZero hp
    letI : NeZero (pairedFrequencyProduct h k) := ⟨pairedFrequencyProduct_ne_zero hs ks⟩
    average (independentMixed d h k hs ks hp hV σ K)=
      coupledAverage outside.prod ((pairedFrequencyProduct h k)^(K+2))
        (mixedTest h k hs ks hp hV σ (residueTransform d))
        (fun z : MixedPair ((pairedFrequencyProduct h k)^(K+2))=>independentRTest K h k σ (z.1,z.2)) := by
  let : NeZero outside.prod := HistorySignedSpectatorDiagramAverage.outsideNeZero hp
  let : NeZero (pairedFrequencyProduct h k) := ⟨pairedFrequencyProduct_ne_zero hs ks⟩
  exact (coupledAverage_eq_nested
    (mixedTest h k hs ks hp hV σ (residueTransform d))
    (fun z : MixedPair ((pairedFrequencyProduct h k)^(K+2))=>independentRTest K h k σ (z.1,z.2))).symm

end Ostmann.Arithmetic.HistoryBulkResidueRootAverage

end

end OAI
