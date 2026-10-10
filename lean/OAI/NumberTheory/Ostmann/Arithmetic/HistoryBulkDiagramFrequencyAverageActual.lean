import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkDiagramFrequencyAverage

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
open HistoryRepresentativeSourceSeparation

theorem actual_canonical_unit_universal
    (had : PairAdmissible h k outside)
    (hm : 0 < m) (hthree : ∀q∈outside,3 ≤ q) :
    letI : NeZero outside.prod := ⟨(outsideModulus_pos hp).ne'⟩
    letI : NeZero (pairedFrequencyProduct h k) := ⟨pairedFrequencyProduct_ne_zero hs ks⟩
    ‖coupledAverage outside.prod ((pairedFrequencyProduct h k)^(K+2))
      (unitTest h k hs ks hp hV σ (residueTransform d)) (fun z : UnitPair ((pairedFrequencyProduct h k)^(K+2))=>canonicalRTest (m:=m) K h k (z.1,z.2))‖ ≤
      (((3:ℝ)^(2^l))^outside.length)*canonicalUnitBulkAverage K h k hs ks m := by
  let : NeZero outside.prod := ⟨(outsideModulus_pos hp).ne'⟩
  let : NeZero (pairedFrequencyProduct h k) := ⟨pairedFrequencyProduct_ne_zero hs ks⟩
  exact canonical_unit_universal d h k hs ks hp hV σ K (had.2.2.2 (K+2)).2.2.2.1 hm hthree

theorem actual_independent_unit_good
    (had : PairAdmissible h k outside)
    (hm : 0 < m) (hthree : ∀q∈outside,3 ≤ q) (hgood : ¬Conclusion.TransferBadArrangement σ) :
    letI : NeZero outside.prod := ⟨(outsideModulus_pos hp).ne'⟩
    letI : NeZero (pairedFrequencyProduct h k) := ⟨pairedFrequencyProduct_ne_zero hs ks⟩
    letI := primeAtNeZero hp
    ‖coupledAverage outside.prod ((pairedFrequencyProduct h k)^(K+2))
      (unitTest h k hs ks hp hV σ (residueTransform d)) (fun z : UnitPair ((pairedFrequencyProduct h k)^(K+2))=>independentRTest K h k σ (z.1,z.2))‖ ≤
      ∏i : Fin outside.length, Tree.treeComparisonConstant (l-2)*
        ((FiniteField.correlationBound (residueTransform d (primeAt outside i)):ℝ)+
          (primeAt outside i:ℝ)^(-(1/4:ℝ))) := by
  let : NeZero outside.prod := ⟨(outsideModulus_pos hp).ne'⟩
  let : NeZero (pairedFrequencyProduct h k) := ⟨pairedFrequencyProduct_ne_zero hs ks⟩
  let := primeAtNeZero hp
  exact independent_unit_good d h k hs ks hp hV σ K (had.2.2.2 (K+2)).2.2.2.1 hm hthree hgood

theorem actual_canonical_mixed_universal
    (had : PairAdmissible h k outside)
    (hm : 0 < m) (hthree : ∀q∈outside,3 ≤ q) :
    letI : NeZero outside.prod := ⟨(outsideModulus_pos hp).ne'⟩
    letI : NeZero (pairedFrequencyProduct h k) := ⟨pairedFrequencyProduct_ne_zero hs ks⟩
    ‖coupledAverage outside.prod ((pairedFrequencyProduct h k)^(K+2))
      (mixedTest h k hs ks hp hV σ (residueTransform d)) (fun z : MixedPair ((pairedFrequencyProduct h k)^(K+2))=>canonicalRTest (m:=m) K h k (z.1,z.2))‖ ≤
      (((3:ℝ)^(2^l))^outside.length)*canonicalRingUnitBulkAverage K h k hs ks m := by
  let : NeZero outside.prod := ⟨(outsideModulus_pos hp).ne'⟩
  let : NeZero (pairedFrequencyProduct h k) := ⟨pairedFrequencyProduct_ne_zero hs ks⟩
  exact canonical_mixed_universal d h k hs ks hp hV σ K (had.2.2.2 (K+2)).2.2.2.1 hm hthree

theorem actual_independent_mixed_good
    (had : PairAdmissible h k outside)
    (hm : 0 < m) (hthree : ∀q∈outside,3 ≤ q) (hgood : ¬Conclusion.TransferBadArrangement σ) :
    letI : NeZero outside.prod := ⟨(outsideModulus_pos hp).ne'⟩
    letI : NeZero (pairedFrequencyProduct h k) := ⟨pairedFrequencyProduct_ne_zero hs ks⟩
    letI := primeAtNeZero hp
    ‖coupledAverage outside.prod ((pairedFrequencyProduct h k)^(K+2))
      (mixedTest h k hs ks hp hV σ (residueTransform d)) (fun z : MixedPair ((pairedFrequencyProduct h k)^(K+2))=>independentRTest K h k σ (z.1,z.2))‖ ≤
      ∏i : Fin outside.length, Tree.treeComparisonConstant (l-2)*
        ((FiniteField.correlationBound (residueTransform d (primeAt outside i)):ℝ)+
          (primeAt outside i:ℝ)^(-(1/4:ℝ))) := by
  let : NeZero outside.prod := ⟨(outsideModulus_pos hp).ne'⟩
  let : NeZero (pairedFrequencyProduct h k) := ⟨pairedFrequencyProduct_ne_zero hs ks⟩
  let := primeAtNeZero hp
  exact independent_mixed_good d h k hs ks hp hV σ K (had.2.2.2 (K+2)).2.2.2.1 hm hthree hgood

end Ostmann.Arithmetic.HistoryBulkDiagramFrequencyAverage

end

end OAI
