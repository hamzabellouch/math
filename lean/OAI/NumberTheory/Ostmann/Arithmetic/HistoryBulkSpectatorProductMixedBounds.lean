import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSpectatorProductMixedMean

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSpectatorProduct
open Construction ResidueHaar HistoryCRTIntegration HistorySignedSpectatorDiagramAverage
open scoped BigOperators

theorem actual_mixed_average_universal (d : Decomposition)
    {l m : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hp : ∀q∈outside,q.Prime) (hV : ∀q∈outside,∀j≤l,V j<q)
    (σ : Equiv.Perm (Fin (2^l)×Fin m)) (hm : 0 < m) (hthree : ∀q∈outside,3≤q) :
    letI := outsideNeZero hp
    letI := primeAtNeZero hp
    ‖average (fun roots : MixedPair outside.prod =>
      average (mixedTest h k hs ks hp hV σ (residueTransform d) roots))‖ ≤
        ((3:ℝ)^(2^l))^outside.length := by
  let := outsideNeZero hp
  let := primeAtNeZero hp
  exact (mixed_average_norm_le_unit h k hs ks hp hV σ (residueTransform d)).trans
    (actual_unit_average_universal d h k hs ks hp hV σ hm hthree)

theorem actual_mixed_average_good (d : Decomposition)
    {l m : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hp : ∀q∈outside,q.Prime) (hV : ∀q∈outside,∀j≤l,V j<q)
    (σ : Equiv.Perm (Fin (2^l)×Fin m)) (hm : 0 < m) (hthree : ∀q∈outside,3≤q)
    (hgood : ¬Conclusion.TransferBadArrangement σ) :
    letI := outsideNeZero hp
    letI := primeAtNeZero hp
    ‖average (fun roots : MixedPair outside.prod =>
      average (mixedTest h k hs ks hp hV σ (residueTransform d) roots))‖ ≤
        ∏i : Fin outside.length, Tree.treeComparisonConstant (l-2)*
          ((FiniteField.correlationBound (residueTransform d (primeAt outside i)) : ℝ)+
            (primeAt outside i : ℝ)^(-(1/4:ℝ))) := by
  let := outsideNeZero hp
  let := primeAtNeZero hp
  exact (mixed_average_norm_le_unit h k hs ks hp hV σ (residueTransform d)).trans
    (actual_unit_average_good d h k hs ks hp hV σ hm hthree hgood)

end Ostmann.Arithmetic.HistoryBulkSpectatorProduct

end

end OAI
