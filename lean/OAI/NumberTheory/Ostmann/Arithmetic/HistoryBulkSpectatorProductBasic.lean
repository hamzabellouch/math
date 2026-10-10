import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSpectatorProductCRT

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSpectatorProduct
open Construction ResidueHaar HistoryCRTIntegration HistoryResidueRegular HistorySignedSpectatorDiagram
open HistoryBulkSpectatorDiagramAverage HistorySignedSpectatorDiagramAverage
open scoped BigOperators

theorem primeAtFact {outside : List ℕ} (hp : ∀q∈outside,q.Prime) :
    ∀i : Fin outside.length, Fact (primeAt outside i).Prime :=
  fun i => ⟨hp _ (List.get_mem outside i)⟩

def localUnitTest {q l m : ℕ} [Fact q.Prime] {V : ℕ → ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hq : q∈outside) (hV : ∀j≤l,V j<q)
    (σ : Equiv.Perm (Fin (2^l)×Fin m)) (g : ZMod q → ℂ)
    (z : JointUnits (Fin (2^l)×Fin m) q) : ℂ :=
  orderedIntegrand σ
    (bulkDiagram h hs (supported_regular h hs hq hV) (denominatorUnit hs hq) z.1.1 z.1.2)
    (bulkDiagram k ks (supported_regular k ks hq hV) (denominatorUnit hs hq) z.1.1 z.1.2) g z.2

def unitTest {l m : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hp : ∀q∈outside,q.Prime) (hV : ∀q∈outside,∀j≤l,V j<q)
    (σ : Equiv.Perm (Fin (2^l)×Fin m)) (g : (q : ℕ) → ZMod q → ℂ)
    (roots : UnitPair outside.prod) (samples : Fin (2^l)×Fin m → (ZMod outside.prod)ˣ) : ℂ :=
  letI := primeAtFact hp
  ∏i : Fin outside.length, localUnitTest h k hs ks (List.get_mem outside i)
    (hV _ (List.get_mem outside i)) σ (g (primeAt outside i))
    (unitProjection (List.dvd_prod (List.get_mem outside i)) (roots,samples))

theorem unit_average_eq_product {l m : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hp : ∀q∈outside,q.Prime) (hV : ∀q∈outside,∀j≤l,V j<q)
    (σ : Equiv.Perm (Fin (2^l)×Fin m)) (g : (q : ℕ) → ZMod q → ℂ) :
    letI := outsideNeZero hp
    letI := primeAtFact hp
    average (fun roots : UnitPair outside.prod => average (unitTest h k hs ks hp hV σ g roots)) =
      ∏i : Fin outside.length, average (fun roots : UnitPair (primeAt outside i) =>
        referenceAverage h k hs ks (List.get_mem outside i) (hV _ (List.get_mem outside i))
          σ (g (primeAt outside i)) roots.1 roots.2) := by
  let := outsideNeZero hp
  let := primeAtFact hp
  let := primeAtNeZero hp
  rw [← average_prod]
  have he := unit_projected_product_average (α:=Fin (2^l)×Fin m)
    (primeAt outside) (primeAt_pairwise h hs) (primeAt_prod outside)
    (fun i => localUnitTest h k hs ks (List.get_mem outside i)
      (hV _ (List.get_mem outside i)) σ (g (primeAt outside i)))
  calc
    _ = ∏i : Fin outside.length, average (localUnitTest h k hs ks (List.get_mem outside i)
        (hV _ (List.get_mem outside i)) σ (g (primeAt outside i))) := he
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact average_prod (fun roots samples => localUnitTest h k hs ks
        (List.get_mem outside i) (hV _ (List.get_mem outside i)) σ
          (g (primeAt outside i)) (roots,samples))

end Ostmann.Arithmetic.HistoryBulkSpectatorProduct

end

end OAI
