import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkDiagramFrequencyAverageCRT
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSpectatorProductMixed

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkDiagramFrequencyAverage
open Construction ResidueHaar HistoryBulkSpectatorProduct HistoryCRTIntegration
open HistoryBulkResidueNormSum HistoryFrequencyResidues HistoryPairedFrequencyAverage
open HistorySignedSpectatorDiagramAverage
open scoped BigOperators
variable (d : Decomposition) {l m : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
variable (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
variable (hp : ∀q∈outside,q.Prime) (hV : ∀q∈outside,∀j≤l,V j<q)
variable (σ : Equiv.Perm (Fin (2^l)×Fin m)) (K : ℕ)
variable [NeZero outside.prod] [NeZero (pairedFrequencyProduct h k)]

theorem canonical_unit_universal
    (hc : outside.prod.Coprime ((pairedFrequencyProduct h k)^(K+2)))
    (hm : 0 < m) (hthree : ∀q∈outside,3 ≤ q) :
    ‖coupledAverage outside.prod ((pairedFrequencyProduct h k)^(K+2))
      (unitTest h k hs ks hp hV σ (residueTransform d)) (fun z : UnitPair ((pairedFrequencyProduct h k)^(K+2))=>canonicalRTest (m:=m) K h k (z.1,z.2))‖ ≤
      (((3:ℝ)^(2^l))^outside.length)*canonicalUnitBulkAverage K h k hs ks m := by
  apply norm_coupledAverage_le hc
  · exact actual_unit_average_universal d h k hs ks hp hV σ hm hthree
  · exact canonical_unit_average_le K h k hs ks

theorem independent_unit_good
    (hc : outside.prod.Coprime ((pairedFrequencyProduct h k)^(K+2)))
    (hm : 0 < m) (hthree : ∀q∈outside,3 ≤ q) (hgood : ¬Conclusion.TransferBadArrangement σ) :
    letI := primeAtNeZero hp
    ‖coupledAverage outside.prod ((pairedFrequencyProduct h k)^(K+2))
      (unitTest h k hs ks hp hV σ (residueTransform d)) (fun z : UnitPair ((pairedFrequencyProduct h k)^(K+2))=>independentRTest K h k σ (z.1,z.2))‖ ≤
      ∏i : Fin outside.length, Tree.treeComparisonConstant (l-2)*
        ((FiniteField.correlationBound (residueTransform d (primeAt outside i)):ℝ)+
          (primeAt outside i:ℝ)^(-(1/4:ℝ))) := by
  let := primeAtNeZero hp
  have hr : ‖average (fun z : UnitPair ((pairedFrequencyProduct h k)^(K+2))=>
      average (independentRTest K h k σ (z.1,z.2)))‖≤1 := by
    apply HistoryBulkSpectatorProduct.norm_average_le
    intro z
    apply HistoryBulkSpectatorProduct.norm_average_le
    intro x
    exact independentRTest_norm_le K h k σ _ x
  have hh := norm_coupledAverage_le hc (unitTest h k hs ks hp hV σ (residueTransform d)) (fun z : UnitPair ((pairedFrequencyProduct h k)^(K+2))=>independentRTest K h k σ (z.1,z.2))
    (actual_unit_average_good d h k hs ks hp hV σ hm hthree hgood) hr
  simpa only [mul_one] using hh

theorem canonical_mixed_universal
    (hc : outside.prod.Coprime ((pairedFrequencyProduct h k)^(K+2)))
    (hm : 0 < m) (hthree : ∀q∈outside,3 ≤ q) :
    ‖coupledAverage outside.prod ((pairedFrequencyProduct h k)^(K+2))
      (mixedTest h k hs ks hp hV σ (residueTransform d)) (fun z : MixedPair ((pairedFrequencyProduct h k)^(K+2))=>canonicalRTest (m:=m) K h k (z.1,z.2))‖ ≤
      (((3:ℝ)^(2^l))^outside.length)*canonicalRingUnitBulkAverage K h k hs ks m := by
  apply norm_coupledAverage_le hc
  · exact actual_mixed_average_universal d h k hs ks hp hV σ hm hthree
  · exact canonical_mixed_average_le K h k hs ks

theorem independent_mixed_good
    (hc : outside.prod.Coprime ((pairedFrequencyProduct h k)^(K+2)))
    (hm : 0 < m) (hthree : ∀q∈outside,3 ≤ q) (hgood : ¬Conclusion.TransferBadArrangement σ) :
    letI := primeAtNeZero hp
    ‖coupledAverage outside.prod ((pairedFrequencyProduct h k)^(K+2))
      (mixedTest h k hs ks hp hV σ (residueTransform d)) (fun z : MixedPair ((pairedFrequencyProduct h k)^(K+2))=>independentRTest K h k σ (z.1,z.2))‖ ≤
      ∏i : Fin outside.length, Tree.treeComparisonConstant (l-2)*
        ((FiniteField.correlationBound (residueTransform d (primeAt outside i)):ℝ)+
          (primeAt outside i:ℝ)^(-(1/4:ℝ))) := by
  let := primeAtNeZero hp
  have hr : ‖average (fun z : MixedPair ((pairedFrequencyProduct h k)^(K+2))=>
      average (independentRTest K h k σ (z.1,z.2)))‖≤1 := by
    apply HistoryBulkSpectatorProduct.norm_average_le
    intro z
    apply HistoryBulkSpectatorProduct.norm_average_le
    intro x
    exact independentRTest_norm_le K h k σ _ x
  have hh := norm_coupledAverage_le hc (mixedTest h k hs ks hp hV σ (residueTransform d)) (fun z : MixedPair ((pairedFrequencyProduct h k)^(K+2))=>independentRTest K h k σ (z.1,z.2))
    (actual_mixed_average_good d h k hs ks hp hV σ hm hthree hgood) hr
  simpa only [mul_one] using hh

end Ostmann.Arithmetic.HistoryBulkDiagramFrequencyAverage

end

end OAI
