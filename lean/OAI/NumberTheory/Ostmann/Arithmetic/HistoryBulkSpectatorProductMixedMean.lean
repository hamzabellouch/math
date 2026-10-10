import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSpectatorProductMixedBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSpectatorProduct
open Construction ResidueHaar HistoryCRTIntegration HistorySignedSpectatorDiagramAverage
attribute [local instance] Classical.propDecidable

theorem average_mixedTest {l m : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hp : ∀q∈outside,q.Prime) (hV : ∀q∈outside,∀j≤l,V j<q)
    (σ : Equiv.Perm (Fin (2^l)×Fin m)) (g : (q : ℕ) → ZMod q → ℂ)
    (roots : MixedPair outside.prod) :
    letI := outsideNeZero hp
    average (mixedTest h k hs ks hp hV σ g roots) =
      rootUnitExtension (fun z => average (unitTest h k hs ks hp hV σ g z)) roots := by
  let _ := outsideNeZero hp
  by_cases hr : IsUnit roots.1
  · rw [rootUnitExtension_eq_of_isUnit _ _ hr]
    congr 1
    funext samples
    exact mixedTest_eq_of_isUnit h k hs ks hp hV σ g roots samples hr
  · simp [mixedTest, rootUnitExtension, hr, average]

theorem mixed_average_eq_unit {l m : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hp : ∀q∈outside,q.Prime) (hV : ∀q∈outside,∀j≤l,V j<q)
    (σ : Equiv.Perm (Fin (2^l)×Fin m)) (g : (q : ℕ) → ZMod q → ℂ) :
    letI := outsideNeZero hp
    average (fun roots : MixedPair outside.prod => average (mixedTest h k hs ks hp hV σ g roots)) =
      ((Nat.totient outside.prod:ℂ)/(outside.prod:ℂ))*
        average (fun roots : UnitPair outside.prod => average (unitTest h k hs ks hp hV σ g roots)) := by
  let _ := outsideNeZero hp
  simp_rw [average_mixedTest]
  exact average_rootUnitExtension _

theorem mixed_average_norm_le_unit {l m : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hp : ∀q∈outside,q.Prime) (hV : ∀q∈outside,∀j≤l,V j<q)
    (σ : Equiv.Perm (Fin (2^l)×Fin m)) (g : (q : ℕ) → ZMod q → ℂ) :
    letI := outsideNeZero hp
    ‖average (fun roots : MixedPair outside.prod => average (mixedTest h k hs ks hp hV σ g roots))‖ ≤
      ‖average (fun roots : UnitPair outside.prod => average (unitTest h k hs ks hp hV σ g roots))‖ := by
  let _ := outsideNeZero hp
  simp_rw [average_mixedTest]
  exact norm_average_rootUnitExtension_le _

end Ostmann.Arithmetic.HistoryBulkSpectatorProduct

end

end OAI
