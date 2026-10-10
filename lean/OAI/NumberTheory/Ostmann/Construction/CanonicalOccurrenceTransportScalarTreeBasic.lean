import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightTree
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportCode

namespace OAI

noncomputable section
namespace Ostmann.Construction.CanonicalOccurrenceTransport
open Arithmetic.HistorySymbolicEncoding Arithmetic.HistorySymbolicState

def rootCode {ι : Type} : {l : ℕ}→TreeCode ι l→StateCode ι
  | 0,e=>e
  | _+1,e=>e.1

def Plan.rootFrequency : {l : ℕ}→Plan l→ℤ
  | _,.leaf s=>s
  | _,.node s _ _ _ _ _ _ _ _=>s

def Plan.leftPlan {l : ℕ} : Plan (l+1)→Plan l
  | .node _ _ _ _ _ _ _ left _=>left

def Plan.rightPlan {l : ℕ} : Plan (l+1)→Plan l
  | .node _ _ _ _ _ _ _ _ right=>right

lemma rootCode_treeCode {ι : Type} {l : ℕ} (h : History l) (e : TreeExpr ι h) :
    rootCode (treeCode h e)=stateCode (treeRoot h e) := by cases h <;> rfl

lemma treeRoot_plus_eq_of_code {ι : Type} {l : ℕ} {h g : History l}
    (e : TreeExpr ι h) (f : TreeExpr ι g) (hc : treeCode h e=treeCode g f) :
    (treeRoot h e).plus=(treeRoot g f).plus := by
  have hh := congrArg rootCode hc
  rw [rootCode_treeCode,rootCode_treeCode] at hh
  exact congrArg StateCode.plus hh

lemma plan_rootFrequency {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) :
    (plan h hs).rootFrequency=h.root.frequency := by cases h <;> rfl

end Ostmann.Construction.CanonicalOccurrenceTransport

end

end OAI
