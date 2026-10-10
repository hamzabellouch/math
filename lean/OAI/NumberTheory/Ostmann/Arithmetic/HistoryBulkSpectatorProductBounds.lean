import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSpectatorProductBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSpectatorProduct
open Construction ResidueHaar HistoryCRTIntegration HistoryBulkSpectatorDiagramAverage
open HistorySignedSpectatorDiagramAverage
open scoped BigOperators

theorem actual_unit_average_universal (d : Decomposition)
    {l m : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hp : ∀q∈outside,q.Prime) (hV : ∀q∈outside,∀j≤l,V j<q)
    (σ : Equiv.Perm (Fin (2^l)×Fin m)) (hm : 0 < m) (hthree : ∀q∈outside,3≤q) :
    letI := outsideNeZero hp
    letI := primeAtNeZero hp
    ‖average (fun roots : UnitPair outside.prod =>
      average (unitTest h k hs ks hp hV σ (residueTransform d) roots))‖ ≤
        ((3:ℝ)^(2^l))^outside.length := by
  let := outsideNeZero hp
  let := primeAtFact hp
  let := primeAtNeZero hp
  rw [unit_average_eq_product, norm_prod]
  calc
    _ ≤ ∏_i : Fin outside.length, (3:ℝ)^(2^l) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro i _
      apply norm_average_le
      intro z
      exact referenceAverage_actual_universal d h k hs ks (List.get_mem outside i)
        (hV _ (List.get_mem outside i)) σ hm (hthree _ (List.get_mem outside i)) z.1 z.2
    _ = _ := by simp

theorem actual_unit_average_good (d : Decomposition)
    {l m : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hp : ∀q∈outside,q.Prime) (hV : ∀q∈outside,∀j≤l,V j<q)
    (σ : Equiv.Perm (Fin (2^l)×Fin m)) (hm : 0 < m) (hthree : ∀q∈outside,3≤q)
    (hgood : ¬Conclusion.TransferBadArrangement σ) :
    letI := outsideNeZero hp
    letI := primeAtNeZero hp
    ‖average (fun roots : UnitPair outside.prod =>
      average (unitTest h k hs ks hp hV σ (residueTransform d) roots))‖ ≤
        ∏i : Fin outside.length, Tree.treeComparisonConstant (l-2)*
          ((FiniteField.correlationBound (residueTransform d (primeAt outside i)) : ℝ)+
            (primeAt outside i : ℝ)^(-(1/4:ℝ))) := by
  let := outsideNeZero hp
  let := primeAtFact hp
  let := primeAtNeZero hp
  rw [unit_average_eq_product, norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro i _
  apply norm_average_le
  intro z
  exact referenceAverage_actual_good d h k hs ks (List.get_mem outside i)
    (hV _ (List.get_mem outside i)) σ hm (hthree _ (List.get_mem outside i)) hgood z.1 z.2

end Ostmann.Arithmetic.HistoryBulkSpectatorProduct

end

end OAI
