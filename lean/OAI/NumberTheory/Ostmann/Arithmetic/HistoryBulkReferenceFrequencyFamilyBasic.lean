import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairedFrequencyAverageHistory
import OAI.NumberTheory.Ostmann.Construction.CanonicalHistoryProductChoices

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceFrequencyFamily
open Construction HistoryPairedFrequencyAverage Characters FrequencyTreeSum

def FrequencyTree : ℕ → Type
  | 0 => ℤ × ℤ
  | l+1 => (ℤ × ℤ) × FrequencyTree l × FrequencyTree l

def eraseAssignment (S : List Bool → Finset (ℤ × ℤ)) :
    {l : ℕ} → {p : List Bool} → Assignment S l p → FrequencyTree l
  | 0, _, a => a.val
  | _l+1, _, a => (a.1.val, eraseAssignment S a.2.1, eraseAssignment S a.2.2)

def choiceTree (V : ℕ → ℕ) : (l : ℕ) → ℤ → ℤ → FrequencyChoices V l → FrequencyChoices V l → FrequencyTree l
  | 0, s, t, _, _ => (s,t)
  | l+1, s, t, f, g => ((s,t),
      choiceTree V l f.1.val g.1.val f.2.2.1 g.2.2.1,
      choiceTree V l f.2.1.val g.2.1.val f.2.2.2 g.2.2.2)

theorem choiceTree_eq_iff (V : ℕ → ℕ) (l : ℕ) (s t s' t' : ℤ)
    (f g f' g' : FrequencyChoices V l) :
    choiceTree V l s t f g = choiceTree V l s' t' f' g' ↔
      (s,t)=(s',t') ∧ f=f' ∧ g=g' := by
  induction l generalizing s t s' t' with
  | zero =>
    cases f; cases g; cases f'; cases g'
    constructor
    · intro he
      exact ⟨he,rfl,rfl⟩
    · intro he
      exact he.1
  | succ l ih =>
    constructor
    · intro he
      have hl := (ih _ _ _ _ _ _ _ _).mp (congrArg (fun z : FrequencyTree (l+1) => z.2.1) he)
      have hr := (ih _ _ _ _ _ _ _ _).mp (congrArg (fun z : FrequencyTree (l+1) => z.2.2) he)
      refine ⟨congrArg (fun z : FrequencyTree (l+1) => z.1) he, ?_, ?_⟩
      · exact Prod.ext (Subtype.ext (congrArg Prod.fst hl.1))
          (Prod.ext (Subtype.ext (congrArg Prod.fst hr.1)) (Prod.ext hl.2.1 hr.2.1))
      · exact Prod.ext (Subtype.ext (congrArg Prod.snd hl.1))
          (Prod.ext (Subtype.ext (congrArg Prod.snd hr.1)) (Prod.ext hl.2.2 hr.2.2))
    · rintro ⟨hroot,rfl,rfl⟩
      rcases Prod.mk.inj hroot with ⟨rfl,rfl⟩
      rfl

theorem erase_historyAssignment_decode (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (S : List Bool → Finset (ℤ × ℤ)) (l : ℕ) (p : List Bool)
    (a b : State) (f g : FrequencyChoices V l)
    (x y : InternalSourceDraws sources seed l)
    (hh : LabelsIn S p
      (decodeHistory sources seed V l a (assembleHistoryChoices sources seed V l f x))
      (decodeHistory sources seed V l b (assembleHistoryChoices sources seed V l g y))) :
    eraseAssignment S (historyAssignment S p
      (decodeHistory sources seed V l a (assembleHistoryChoices sources seed V l f x))
      (decodeHistory sources seed V l b (assembleHistoryChoices sources seed V l g y)) hh) =
      choiceTree V l a.frequency b.frequency f g := by
  induction l generalizing p a b with
  | zero => rfl
  | succ l ih =>
    simp only [assembleHistoryChoices, decodeHistory, historyAssignment, eraseAssignment, choiceTree]
    exact Prod.ext rfl (Prod.ext (ih _ _ _ _ _ _ _ _) (ih _ _ _ _ _ _ _ _))

theorem supported_assignment_decode_injective (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ)
    (sources : SourceFamily) (seed : List SourceSlot) (l : ℕ) (outside : List ℕ)
    (a b a' b' : State)
    (f g f' g' : FrequencyChoices (Conclusion.frequencyBound Bs BD Bz k L) l)
    (x y x' y' : InternalSourceDraws sources seed l)
    (ha : (decodeHistory sources seed _ l a (assembleHistoryChoices sources seed _ l f x)).Supported
      (Conclusion.frequencyBound Bs BD Bz k L) outside)
    (hb : (decodeHistory sources seed _ l b (assembleHistoryChoices sources seed _ l g y)).Supported
      (Conclusion.frequencyBound Bs BD Bz k L) outside)
    (ha' : (decodeHistory sources seed _ l a' (assembleHistoryChoices sources seed _ l f' x')).Supported
      (Conclusion.frequencyBound Bs BD Bz k L) outside)
    (hb' : (decodeHistory sources seed _ l b' (assembleHistoryChoices sources seed _ l g' y')).Supported
      (Conclusion.frequencyBound Bs BD Bz k L) outside)
    (he : supportedHistoryAssignment Bs BD Bz k L _ _ ha hb =
      supportedHistoryAssignment Bs BD Bz k L _ _ ha' hb') : f=f' ∧ g=g' := by
  have ht := congrArg (eraseAssignment (PairedFrequencyActualBudget.pairedRanges Bs BD Bz k L l)) he
  simp only [supportedHistoryAssignment, erase_historyAssignment_decode] at ht
  exact ((choiceTree_eq_iff _ _ _ _ _ _ _ _ _ _).mp ht).2

end Ostmann.Arithmetic.HistoryBulkReferenceFrequencyFamily

end

end OAI
