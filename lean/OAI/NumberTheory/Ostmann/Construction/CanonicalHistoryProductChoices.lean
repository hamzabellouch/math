import OAI.NumberTheory.Ostmann.Construction.CanonicalHistoryProductChoicesDefs

namespace OAI

noncomputable section
namespace Ostmann.Construction
open CanonicalOccurrenceTransport
open scoped BigOperators

@[simp] theorem assembleHistoryChoices_projections (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ → ℕ) (l : ℕ) (c : HistoryChoices sources seed V l) :
    assembleHistoryChoices sources seed V l
      (historyFrequencies sources seed V l c) (historyDraws sources seed V l c)=c := by
  induction l with
  | zero => cases c; rfl
  | succ l ih =>
    rcases c with ⟨v,w,x,left,right⟩
    simp only [assembleHistoryChoices,historyFrequencies,historyDraws,ih]
    rfl

@[simp] theorem historyFrequencies_assemble (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ → ℕ) (l : ℕ) (f : FrequencyChoices V l)
    (x : InternalSourceDraws sources seed l) :
    historyFrequencies sources seed V l (assembleHistoryChoices sources seed V l f x)=f := by
  induction l with
  | zero => cases f; rfl
  | succ l ih =>
    rcases f with ⟨v,w,left,right⟩
    simp only [assembleHistoryChoices,historyFrequencies]
    exact congrArg₂ (fun a b => (v, w, a, b))
      (ih left (fun i => x (.inr (.inl i))))
      (ih right (fun i => x (.inr (.inr i))))

@[simp] theorem historyDraws_assemble (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ → ℕ) (l : ℕ) (f : FrequencyChoices V l)
    (x : InternalSourceDraws sources seed l) :
    historyDraws sources seed V l (assembleHistoryChoices sources seed V l f x)=x := by
  induction l with
  | zero => funext i; exact Empty.elim i
  | succ l ih =>
    funext i
    rcases i with i | i | i
    · rfl
    · exact congrFun (ih f.2.2.1 (fun j => x (.inr (.inl j)))) i
    · exact congrFun (ih f.2.2.2 (fun j => x (.inr (.inr j)))) i

def historyChoicesProductEquiv (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) :
    HistoryChoices sources seed V l ≃ FrequencyChoices V l × InternalSourceDraws sources seed l where
  toFun c := ⟨historyFrequencies sources seed V l c,historyDraws sources seed V l c⟩
  invFun z := assembleHistoryChoices sources seed V l z.1 z.2
  left_inv c := assembleHistoryChoices_projections sources seed V l c
  right_inv z := Prod.ext (historyFrequencies_assemble sources seed V l z.1 z.2)
    (historyDraws_assemble sources seed V l z.1 z.2)

theorem sum_historyChoices_eq {A : Type*} [AddCommMonoid A]
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ) (l : ℕ)
    (F : HistoryChoices sources seed V l → A) :
    (∑ c : HistoryChoices sources seed V l,F c) =
      ∑ f : FrequencyChoices V l,∑ x : InternalSourceDraws sources seed l,
        F (assembleHistoryChoices sources seed V l f x) := by
  classical
  let e := historyChoicesProductEquiv sources seed V l
  have hh := Fintype.sum_equiv e F (fun z => F (e.symm z))
    (fun c => by rw [Equiv.symm_apply_apply])
  have hei (z : FrequencyChoices V l × InternalSourceDraws sources seed l) :
      e.symm z=assembleHistoryChoices sources seed V l z.1 z.2 := rfl
  simpa only [Fintype.sum_prod_type,hei] using hh

end Ostmann.Construction

end

end OAI
