import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConversePlanPositive
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightPositiveSupportActual
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportNormalized

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConversePlan
open Construction Construction.CanonicalOccurrenceTransport
open Characters.RationalHistory HistorySymbolicEncoding HistorySymbolicState
open HistoryOccurrenceVariables

variable {ι κ : Type}

lemma rootCode_rename_treeCode (f : ι → κ) {l : ℕ}
    (h : History l) (e : TreeExpr ι h) :
    rootCode (renameTree f (treeCode h e)) = (stateCode (treeRoot h e)).rename f := by
  cases h <;> rfl

theorem codePivotsPositive_rename_treeCode_iff (f : ι → κ) (x : κ → ℚ)
    {l : ℕ} (h : History l) (e : TreeExpr ι h) :
    CodePivotsPositive x (renameTree f (treeCode h e)) ↔
      AllPivotsPositive (fun i => (x (f i) : ℝ)) h e := by
  induction h with
  | leaf a => rfl
  | node a p u hp hm left right ihl ihr =>
    simp only [CodePivotsPositive,renameTree,treeCode,rootCode_rename_treeCode,
      StateCode.rename,stateCode,Expr.rationalEval_rename,
      AllPivotsPositive,AllPivots,ihl,ihr]
    rw [show (fun i => (x (f i) : ℝ)) = (fun i => ((x ∘ f) i : ℝ)) from rfl,
      Expr.realEval_cast_rational]
    simp only [Rat.cast_pos]

theorem codePivotsPositive_execute_of_actualRealHistoryScalar_ne_zero
    (b s : ℕ) (X tb td G : ℝ) (outside : List ℕ)
    (seed : List SourceSlot) {l : ℕ} {V : ℕ → ℕ}
    (h : History l) (hs : h.Supported V outside) (hh : TreeSourceLabels seed h)
    (x : Coordinate seed l → ℚ)
    (hz : actualRealHistoryScalar b s X tb td G outside h hs
      (fun k => (x ((coordinateEquiv seed h hh).symm k) : ℝ)) ≠ 0) :
    CodePivotsPositive x (execute (plan h hs) (fixedRootCode seed l)
      (fixedCompensationCode seed l (fun i => .atom (.inr (.inr i))))) := by
  rw [← normalizedCode_eq_execute seed h hs hh]
  apply (codePivotsPositive_rename_treeCode_iff _ x h (symbolicHistory h hs)).mpr
  exact allPivotsPositive_of_actualRealHistoryScalar_ne_zero
    b s X tb td G outside h hs _ hz

end Ostmann.Arithmetic.HistoryBulkSupportConversePlan

end

end OAI
