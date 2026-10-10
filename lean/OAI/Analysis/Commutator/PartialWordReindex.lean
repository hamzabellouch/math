import Mathlib
import OAI.Analysis.Commutator.PartialWordPerturbation

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching.Words

variable {A J K J' K' : Type*} [CStarAlgebra A]

def mapLetter (f : J' → J) (g : K' → K) (i : Letter J' K') : Letter J K :=
  (f i.1,i.2.map (Option.map g))

lemma valid_cons_iff (i : Letter J K) (l : List (Letter J K)) :
    Valid (i::l) ↔ Valid l ∧ (l≠[] → NonzeroSlot i.2) := by
  constructor
  · intro h
    constructor
    · intro s j t he ht
      exact h (i::s) j t (by simpa only [List.cons_append] using congrArg (List.cons i) he) ht
    · intro hl
      exact h [] i l rfl hl
  · rintro ⟨hl,hi⟩ s j t he ht
    cases s with
    | nil =>
      have hh := List.cons.inj he
      obtain ⟨rfl,rfl⟩ := hh
      exact hi ht
    | cons a s =>
      have hh := List.cons.inj he
      exact hl s j t hh.2 ht

lemma valid_map (f : J' → J) (g : K' → K) {l : List (Letter J' K')} (h : Valid l) :
    Valid (l.map (mapLetter f g)) := by
  induction l with
  | nil =>
    intro s i t he ht
    have hh := congrArg List.length he
    simp only [List.map_nil,List.length_nil,List.length_append,List.length_cons] at hh
    omega
  | cons i l ih =>
    rw [List.map_cons,valid_cons_iff]
    have hh := (valid_cons_iff i l).mp h
    refine ⟨ih hh.1,?_⟩
    intro hn
    have hl : l≠[] := by intro he; subst l; exact hn rfl
    obtain ⟨k,hk⟩ := hh.2 hl
    refine ⟨g k,?_⟩
    simp [mapLetter,hk]

lemma slotPower_reindex (k : K → ℤ) (g : K' → K) (v : PartialUnitary A) (s : Slot K') :
    slotPower k v (s.map (Option.map g))=slotPower (k ∘ g) v s := by
  cases s with
  | none => rfl
  | some s => cases s <;> rfl

lemma letter_reindex (x : J → A) (k : K → ℤ) (f : J' → J) (g : K' → K)
    (v : PartialUnitary A) (i : Letter J' K') :
    letter x k v (mapLetter f g i)=letter (x ∘ f) (k ∘ g) v i := by
  exact congrArg (x (f i.1)*·) (slotPower_reindex k g v i.2)

lemma word_reindex (x : J → A) (k : K → ℤ) (f : J' → J) (g : K' → K)
    (v : PartialUnitary A) (l : List (Letter J' K')) :
    word x k v (l.map (mapLetter f g))=word (x ∘ f) (k ∘ g) v l := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.map_cons,word_cons,letter_reindex,ih]

variable [PartialOrder A]

lemma momentBound_reindex (τ : A →ₚ[ℂ] ℂ) (x : J → A) (k : K → ℤ)
    (f : J' → J) (g : K' → K) (v : PartialUnitary A) {N : ℕ} {B : ℝ}
    (h : MomentBound τ x k v N B) : MomentBound τ (x ∘ f) (k ∘ g) v N B := by
  refine ⟨fun i => h.1 (g i),?_⟩
  intro l hn hl hv
  rw [←word_reindex]
  exact h.2 _ (by intro he; apply hn; exact List.length_eq_zero_iff.mp (by simpa only [List.length_map,List.length_nil] using congrArg List.length he)) (by simpa only [List.length_map] using hl)
    (valid_map f g hv)

end Kadison.FinitePatching.Words

end

end
end

end OAI
