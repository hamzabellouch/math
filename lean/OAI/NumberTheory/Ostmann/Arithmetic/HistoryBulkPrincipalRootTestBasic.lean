import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedIntegralReplacementTests
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRawSamples

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkPrincipalRootTest
open Construction ResidueHaar HistoryBulkSelectedIntegralReplacement HistoryBulkResidueRootAverage
open HistoryBulkResidueNormSum HistoryBulkSpectatorProduct HistoryFrequencyResidues HistoryCRTIntegration

theorem average_separated {α β : Type*} [Fintype α] [Fintype β]
    (f : α→ℂ) (g : β→ℂ) :
    average (fun a=>average (fun b=>f a*g b))=average f*average g := by
  simp only [average,←Finset.mul_sum,←Finset.sum_mul]
  ring

variable (d : Decomposition) {l m : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hp : ∀q∈outside,q.Prime) (hV : ∀q∈outside,∀j≤l,V j<q)
    (σ : Equiv.Perm (Fin (2^l)×Fin m)) (K : ℕ)
    [NeZero outside.prod] [NeZero (pairedFrequencyProduct h k)]
    (x : Fin (2^l)×Fin m→(ZMod (outside.prod*(pairedFrequencyProduct h k)^(K+2)))ˣ)

theorem independent_unit_eq_product :
    rootTest true false d h k hs ks hp hV σ K x=
      average (fun z : UnitPair outside.prod=>
        unitTest h k hs ks hp hV σ (residueTransform d) z
          (fun i=>ZMod.unitsMap (Nat.dvd_mul_right _ _) (x i)))*
      average (fun z : UnitPair ((pairedFrequencyProduct h k)^(K+2))=>
        independentRTest K h k σ ((z.1:ZMod ((pairedFrequencyProduct h k)^(K+2))),
          (z.2:ZMod ((pairedFrequencyProduct h k)^(K+2))))
          (fun i=>ZMod.unitsMap (Nat.dvd_mul_left _ _) (x i))) := by
  change average (fun zD=>average (fun zR=>_))=_
  exact average_separated _ _

theorem independent_mixed_eq_product :
    rootTest true true d h k hs ks hp hV σ K x=
      average (fun z : MixedPair outside.prod=>
        mixedTest h k hs ks hp hV σ (residueTransform d) z
          (fun i=>ZMod.unitsMap (Nat.dvd_mul_right _ _) (x i)))*
      average (fun z : MixedPair ((pairedFrequencyProduct h k)^(K+2))=>
        independentRTest K h k σ ((z.1:ZMod ((pairedFrequencyProduct h k)^(K+2))),
          (z.2:ZMod ((pairedFrequencyProduct h k)^(K+2))))
          (fun i=>ZMod.unitsMap (Nat.dvd_mul_left _ _) (x i))) := by
  change average (fun zD=>average (fun zR=>_))=_
  exact average_separated _ _

theorem canonical_unit_eq_product :
    rootTest false false d h k hs ks hp hV σ K x=
      average (fun z : UnitPair outside.prod=>
        unitTest h k hs ks hp hV σ (residueTransform d) z
          (fun i=>ZMod.unitsMap (Nat.dvd_mul_right _ _) (x i)))*
      average (fun z : UnitPair ((pairedFrequencyProduct h k)^(K+2))=>
        canonicalRTest K h k ((z.1:ZMod ((pairedFrequencyProduct h k)^(K+2))),
          (z.2:ZMod ((pairedFrequencyProduct h k)^(K+2))))
          (fun i=>ZMod.unitsMap (Nat.dvd_mul_left _ _) (x i))) := by
  change average (fun zD=>average (fun zR=>_))=_
  exact average_separated _ _

theorem canonical_mixed_eq_product :
    rootTest false true d h k hs ks hp hV σ K x=
      average (fun z : MixedPair outside.prod=>
        mixedTest h k hs ks hp hV σ (residueTransform d) z
          (fun i=>ZMod.unitsMap (Nat.dvd_mul_right _ _) (x i)))*
      average (fun z : MixedPair ((pairedFrequencyProduct h k)^(K+2))=>
        canonicalRTest K h k ((z.1:ZMod ((pairedFrequencyProduct h k)^(K+2))),
          (z.2:ZMod ((pairedFrequencyProduct h k)^(K+2))))
          (fun i=>ZMod.unitsMap (Nat.dvd_mul_left _ _) (x i))) := by
  change average (fun zD=>average (fun zR=>_))=_
  exact average_separated _ _

end Ostmann.Arithmetic.HistoryBulkPrincipalRootTest

end

end OAI
