import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportRename

namespace OAI

noncomputable section
namespace Ostmann.Construction.CanonicalOccurrenceTransport
open Arithmetic.HistoryOccurrenceVariables Arithmetic.HistorySymbolicEncoding
open Arithmetic.HistorySymbolicState Characters.RationalHistory

lemma ofFn_finCongr {A : Type} {m n : ℕ} (h : m=n) (f : Fin n → A) :
    List.ofFn (fun i => f (finCongr h i))=List.ofFn f := by
  subst n
  rfl

def fixedRootCode (seed : List SourceSlot) (l : ℕ) : StateCode (Coordinate seed l) :=
  ⟨.atom (.inl false),.atom (.inl true),List.ofFn fun i => .atom (.inr (.inl i))⟩

def fixedCompensationCode {ι : Type} (seed : List SourceSlot) :
    (l:ℕ) → (Internal seed l → Expr ι) → CompensationCode ι l
  | 0,_ => ()
  | _+1,c => (List.ofFn fun i => c (.inl i),
      fixedCompensationCode seed _ (fun i => c (.inr (.inl i))),
      fixedCompensationCode seed _ (fun i => c (.inr (.inr i))))

lemma root_code_normalized (seed : List SourceSlot) {l : ℕ}
    (h : History l) (hh : TreeSourceLabels seed h) :
    (stateCode (rootExpr h)).rename (coordinateEquiv seed h hh).symm=fixedRootCode seed l := by
  apply StateCode.ext
  · rfl
  · rfl
  · simp only [stateCode,StateCode.rename,rootExpr,fixedRootCode,List.map_ofFn]
    change List.ofFn (fun i : Fin h.root.small.length => (Expr.atom (Sum.inr (Sum.inl
      (finCongr (Template.matches_length (root_matches hh)) i))) : Expr (Coordinate seed l)))=_
    exact ofFn_finCongr (Template.matches_length (root_matches hh))
      (fun i => (Expr.atom (.inr (.inl i)) : Expr (Coordinate seed l)))

lemma compensation_code_fixed {ι : Type} (seed : List SourceSlot) {l : ℕ}
    (h : History l) (hh : TreeSourceLabels seed h) (c : Internal seed l → Expr ι) :
    compensationCode h (fun i => c ((internalEquiv seed h hh).symm i))=
      fixedCompensationCode seed l c := by
  induction h with
  | leaf a => rfl
  | node a p u hp hm left right ihl ihr =>
    simp only [compensationCode,fixedCompensationCode,internalEquiv,Equiv.sumCongr_symm,
      Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr]
    apply Prod.ext
    · simpa only [finCongr_symm] using ofFn_finCongr (Template.matches_length hh.2.2.2.1) (fun i => c (.inl i))
    · exact Prod.ext (ihl hh.2.2.2.2.1 (fun i => c (.inr (.inl i))))
        (ihr hh.2.2.2.2.2 (fun i => c (.inr (.inr i))))

lemma compensation_code_normalized (seed : List SourceSlot) {l : ℕ}
    (h : History l) (hh : TreeSourceLabels seed h) :
    renameCompensation (coordinateEquiv seed h hh).symm (compensationCode h (compensationExpr h))=
      fixedCompensationCode seed l (fun i => .atom (.inr (.inr i))) := by
  rw [compensationCode_rename]
  have hc : (fun i => (compensationExpr h i).rename (coordinateEquiv seed h hh).symm)=
      (fun i => Expr.atom (.inr (.inr ((internalEquiv seed h hh).symm i)))) := by
    funext i
    obtain ⟨j,rfl⟩ := (internalEquiv seed h hh).surjective i
    simp
  rw [hc]
  exact compensation_code_fixed seed h hh (fun i => (Expr.atom (.inr (.inr i)) : Expr (Coordinate seed l)))

def normalizedCode (seed : List SourceSlot) {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (hh : TreeSourceLabels seed h) :
    TreeCode (Coordinate seed l) l :=
  renameTree (coordinateEquiv seed h hh).symm (treeCode h (symbolicHistory h hs))

theorem normalizedCode_eq_execute (seed : List SourceSlot) {l : ℕ} {V : ℕ → ℕ}
    {outside : List ℕ} (h : History l) (hs : h.Supported V outside)
    (hh : TreeSourceLabels seed h) :
    normalizedCode seed h hs hh=execute (plan h hs) (fixedRootCode seed l)
      (fixedCompensationCode seed l (fun i => .atom (.inr (.inr i)))) := by
  rw [normalizedCode,symbolicHistory,encode_code,execute_rename,
    root_code_normalized,compensation_code_normalized]

end Ostmann.Construction.CanonicalOccurrenceTransport

end

end OAI
