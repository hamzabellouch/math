import Mathlib
import OAI.GroupTheory.SimpleOvergroups.FamilyProgram

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
open FiniteAlgebraicEnvelopes Bootstrap
noncomputable section
open scoped Classical

namespace FiniteParameter
variable {I X Y : Type*} [Primcodable I] [Primcodable X] [Primcodable Y]
  [DecidableEq I] (f : I → X → Part Y)

def select (l : List I) (p : I × X) : Part Y :=
  l.foldr (fun i rest => if p.1 = i then f i p.2 else rest) Part.none

theorem select_partrec (hf : ∀ i, Partrec (f i)) (l : List I) : Partrec (select f l) := by
  induction l with
  | nil => exact Partrec.none
  | cons i l ih =>
    exact (Partrec.cond (Primrec.eq.comp Primrec.fst (Primrec.const i)).decide.to_comp
      ((hf i).comp Computable.snd) ih).of_eq (by
        intro p
        simp only [select,List.foldr_cons]
        split <;> simp_all)

omit [Primcodable I] [Primcodable X] [Primcodable Y] in
theorem select_mem [Primcodable I] [Primcodable X] [Primcodable Y]
    (l : List I) (p : I × X) (hp : p.1 ∈ l) : select f l p = f p.1 p.2 := by
  induction l with
  | nil => simp at hp
  | cons i l ih =>
    simp only [select,List.foldr_cons]
    split
    next h => simp only [h]
    next h => exact ih ((List.mem_cons.mp hp).resolve_left h)

theorem partrec₂ [Fintype I] (hf : ∀ i, Partrec (f i)) : Partrec₂ f :=
  (select_partrec f hf (Static.letters I)).of_eq (fun p => select_mem f _ p (by simp [Static.letters]))
end FiniteParameter

namespace FamilyProgram
variable {I P S : Type*} {A Q : I → Type*}
  [Fintype I] [Fintype S] [Primcodable I] [Primcodable P] [Primcodable S]
  [∀ i, Primcodable (A i)] [∀ i, Primcodable (Q i)]
  [DecidableEq I] [DecidableEq S] [∀ i, DecidableEq (A i)] [∀ i, DecidableEq (Q i)]
variable {r : S → S → Prop} [DecidableRel (List.Shortlex r)]
variable (C : ∀ i, DelimiterCode (A i) S) (E : ∀ i, FiniteSearch (C i)) (z : S)

omit [∀ index, DecidableEq (A index)] in
 theorem partrec_compute [∀ index, DecidableEq (A index)]
    (hw : ∀ i, Primrec (E i).words) (hc : ∀ i, Primrec (C i).encode)
    (hl : PrimrecRel (List.Shortlex r))
    {f : ∀ i, P → List (A i) → Part (Option (Q i))}
    (hf : ∀ i, Partrec₂ (f i)) :
    Partrec₂ (fun p => compute (r:=r) C E z (fun i => f i p)) := by
  have hi : Partrec₂ (fun i (x : P × ℕ) => CodedSearch.compute (r:=r) (C i) (E i) z (f i x.1) x.2) :=
    FiniteParameter.partrec₂ _ (fun i => CodedProgram.partrec_search (C i) (E i) z (hw i) (hc i) hl (hf i))
  have ht : Partrec₂ (fun x : P × ℕ => fun i => CodedSearch.compute (r:=r) (C i) (E i) z (f i x.1) x.2) :=
    hi.comp Computable.snd Computable.fst
  have hs : Partrec (fun x : P × ℕ =>
      (Effect.traverse (fun i => CodedSearch.compute (r:=r) (C i) (E i) z (f i x.1) x.2)
        (Static.letters I)).map (fun rs => Base.absorption z ++ rs.flatten)) :=
    ((Effect.partrec_traverse_parameter ht).comp Computable.id (Computable.const _)).map
      ((Primrec.list_append.comp (Primrec.const (Base.absorption z))
        (Primrec.list_flatten.comp Primrec.snd)).to_comp).to₂
  exact (Partrec.cond ((Primrec.eq.comp Primrec.snd (Primrec.const 0)).decide.to_comp)
    (Computable.const (Base.absorption z)).partrec hs).of_eq (by
      intro x
      simp only [compute]
      split <;> simp_all)
end FamilyProgram
end
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
