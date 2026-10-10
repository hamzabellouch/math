import Mathlib
import OAI.GroupTheory.BooneHigman.Basic
import OAI.GroupTheory.SimpleOvergroups.FamilyTables

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
noncomputable section
open FiniteAlgebraicEnvelopes Bootstrap

namespace DelimiterCode
variable {A S T : Type*}

def map (C : DelimiterCode A S) (f : S → T) (hf : Function.Injective f) : DelimiterCode A T where
  start := f C.start
  stop := f C.stop
  distinct := fun h => C.distinct (hf h)
  body a := (C.body a).map f
  start_avoids a := by
    simpa only [List.mem_map, hf.eq_iff, exists_eq_right] using C.start_avoids a
  stop_avoids a := by
    simpa only [List.mem_map, hf.eq_iff, exists_eq_right] using C.stop_avoids a
  injective := fun _ _ h => C.injective (List.map_injective_iff.mpr hf h)

@[simp] theorem map_block (C : DelimiterCode A S) (f : S → T) (hf : Function.Injective f) (a : A) :
    (C.map f hf).block a = (C.block a).map f := by simp [map,block]

@[simp] theorem map_encode (C : DelimiterCode A S) (f : S → T) (hf : Function.Injective f) (w : List A) :
    (C.map f hf).encode w = (C.encode w).map f := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [encode_cons,map_block,ih,List.map_append]

theorem map_alphabet (C : DelimiterCode A S) (f : S → T) (hf : Function.Injective f) :
    (C.map f hf).alphabet ⊆ Set.range f := by
  intro t ht
  rcases ht with h | h | ⟨a,ha⟩
  · exact ⟨C.start,h.symm⟩
  · exact ⟨C.stop,h.symm⟩
  · obtain ⟨s,_,hs⟩ := List.mem_map.mp ha
    exact ⟨s,hs⟩

def searchMap (C : DelimiterCode A S) (E : FiniteSearch C)
    (f : S → T) (hf : Function.Injective f) : FiniteSearch (C.map f hf) where
  words := E.words
  mem_words := by intro n w; simpa only [map_encode,List.length_map] using E.mem_words n w

end DelimiterCode

namespace ThreeCodes
abbrev Alphabet := Option (Fin 3 × Fin 4)
def inclusion (i : Fin 3) (a : Fin 4) : Alphabet := some (i,a)
theorem inclusion_injective (i : Fin 3) : Function.Injective (inclusion i) := by
  intro a b h
  exact (Prod.mk.inj (Option.some.inj h)).2

def code {A : Type*} [Encodable A] (i : Fin 3) (cost : A → ℕ) : DelimiterCode A Alphabet :=
  (PaddedCode.code cost).map (inclusion i) (inclusion_injective i)

def search {A : Type*} [Encodable A] (i : Fin 3) (cost : A → ℕ) : FiniteSearch (code i cost) where
  words := PaddedCode.words cost
  mem_words n w := by simpa only [code,DelimiterCode.map_encode,List.length_map] using PaddedCode.mem_words cost n w

theorem cost_padding {A : Type*} [Encodable A] (i : Fin 3) (cost : A → ℕ) (a : A) :
    10 * cost a + 2 ≤ ((code i cost).block a).length := by
  simpa only [code,DelimiterCode.map_block,List.length_map] using PaddedCode.cost_padding cost a

theorem zero_avoids {A : Type*} [Encodable A] (i : Fin 3) (cost : A → ℕ) :
    none ∉ (code i cost).alphabet := by
  intro h
  obtain ⟨a,ha⟩ := (PaddedCode.code cost).map_alphabet (inclusion i) (inclusion_injective i) h
  cases ha

theorem disjoint {A B : Type*} [Encodable A] [Encodable B] {i j : Fin 3}
    (hi : i ≠ j) (c : A → ℕ) (d : B → ℕ) :
    Disjoint (code i c).alphabet (code j d).alphabet := by
  apply Set.disjoint_left.mpr
  intro t ht hu
  obtain ⟨a,ha⟩ := (PaddedCode.code c).map_alphabet (inclusion i) (inclusion_injective i) ht
  obtain ⟨b,hb⟩ := (PaddedCode.code d).map_alphabet (inclusion j) (inclusion_injective j) hu
  exact hi (Prod.mk.inj (Option.some.inj (ha.trans hb.symm))).1

theorem primrec_encode {A : Type*} [Primcodable A] (i : Fin 3) (cost : A → ℕ) (hc : Primrec cost) :
    Primrec (code i cost).encode := by
  exact (Primrec.list_map (PaddedCode.primrec_encode cost hc)
    ((Primrec.dom_finite (inclusion i)).comp Primrec.snd).to₂).of_eq (fun w => (DelimiterCode.map_encode ..).symm)

theorem primrec_words {A : Type*} [Primcodable A] (i : Fin 3) (cost : A → ℕ) (hc : Primrec cost) :
    Primrec (search i cost).words := PaddedCode.primrec_words cost hc

end ThreeCodes
end
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
