import Mathlib
import OAI.Computability.FiniteCompiler.Rewriting
import OAI.Computability.FiniteCompiler.Selectors
import OAI.GroupTheory.SimpleOvergroups.EffectiveCode

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
open FiniteAlgebraicEnvelopes.Bootstrap Relation

structure FiniteSearch {A S : Type*} (C : DelimiterCode A S) where
  words : ℕ → List (List A)
  mem_words : ∀ n w, w ∈ words n ↔ (C.encode w).length ≤ n

namespace PaddedCode
variable {A : Type*} [Encodable A] (cost : A → ℕ)
def search : FiniteSearch (code cost) := ⟨words cost, mem_words cost⟩
end PaddedCode

namespace EncodedCanonical
variable {A S Q : Type*} {r : S → S → Prop}
variable (C : DelimiterCode A S) (wf : WellFounded r) [Std.Trichotomous r]
  (q : List A → Q)

def candidates (w : List A) : Set (List A) :=
  {v | (C.encode v).length ≤ (C.encode w).length ∧ q v = q w}

noncomputable def least (w : List A) : List A :=
  (InvImage.wf C.encode (List.Shortlex.wf wf)).min (candidates C q w) ⟨w, le_rfl, rfl⟩

omit [Std.Trichotomous r] in
theorem least_mem [Std.Trichotomous r] (w : List A) : least C wf q w ∈ candidates C q w :=
  (InvImage.wf C.encode (List.Shortlex.wf wf)).min_mem _ _

theorem least_length (w : List A) : (C.encode (least C wf q w)).length ≤ (C.encode w).length :=
  (least_mem C wf q w).1

theorem least_class (w : List A) : q (least C wf q w) = q w := (least_mem C wf q w).2

omit [Std.Trichotomous r] in
theorem least_min [Std.Trichotomous r] {w v : List A} (hv : (C.encode v).length ≤ (C.encode w).length)
    (hq : q v = q w) : ¬ List.Shortlex r (C.encode v) (C.encode (least C wf q w)) :=
  (InvImage.wf C.encode (List.Shortlex.wf wf)).not_lt_min (candidates C q w) ⟨hv, hq⟩

theorem least_lt_or_eq (w : List A) :
    List.Shortlex r (C.encode (least C wf q w)) (C.encode w) ∨ least C wf q w = w := by
  by_cases h : List.Shortlex r (C.encode (least C wf q w)) (C.encode w)
  · exact Or.inl h
  · exact Or.inr (C.encode_injective
      (Std.Trichotomous.trichotomous _ _ h (least_min C wf q le_rfl rfl)))

theorem least_global_min {w v : List A} (hq : q v = q w) :
    ¬ List.Shortlex r (C.encode v) (C.encode (least C wf q w)) := by
  intro hd
  have hlen : (C.encode v).length ≤ (C.encode w).length := by
    have hm := least_length C wf q w
    have he := List.shortlex_def.mp hd
    omega
  exact least_min C wf q hlen hq hd

theorem least_congr {u v : List A} (hq : q u = q v) : least C wf q u = least C wf q v := by
  apply C.encode_injective
  exact Std.Trichotomous.trichotomous _ _
    (least_global_min C wf q ((least_class C wf q u).trans hq))
    (least_global_min C wf q ((least_class C wf q v).trans hq.symm))

theorem least_idem (w : List A) : least C wf q (least C wf q w) = least C wf q w :=
  least_congr C wf q (least_class C wf q w)

theorem least_nil : least C wf q [] = [] := by
  have h := least_length C wf q []
  have h' : C.encode (least C wf q []) = [] := List.length_eq_zero_iff.mp (by simpa using h)
  exact (C.encode_eq_nil _).mp h'

theorem eq_least_iff {w v : List A} : v = least C wf q w ↔
    (C.encode v).length ≤ (C.encode w).length ∧ q v = q w ∧
      ∀ t, (C.encode t).length ≤ (C.encode w).length → q t = q w →
        ¬ List.Shortlex r (C.encode t) (C.encode v) := by
  constructor
  · rintro rfl
    exact ⟨least_length C wf q w, least_class C wf q w, fun _ ht hq => least_min C wf q ht hq⟩
  · rintro ⟨hv, hq, hm⟩
    apply C.encode_injective
    exact Std.Trichotomous.trichotomous _ _ (least_min C wf q hv hq)
      (hm _ (least_length C wf q w) (least_class C wf q w))
end EncodedCanonical

namespace CodeTable
variable {A S Q : Type*} {r : S → S → Prop} [Std.Trichotomous r]
variable (C : DelimiterCode A S) (E : FiniteSearch C) (wf : WellFounded r)
  (q : List A → Option Q) (z : S)

noncomputable def output (v : List A) : List S :=
  if q v = none then [z] else C.encode (EncodedCanonical.least C wf q v)

noncomputable def table (n : ℕ) : List (List S × List S) := by
  classical
  exact ((E.words n).filter fun v => v ≠ [] ∧ output C wf q z v ≠ C.encode v).map
    (fun v => (C.encode v, output C wf q z v))

omit [Std.Trichotomous r] in
theorem mem_table [Std.Trichotomous r] {n : ℕ} {a b : List S} : (a,b) ∈ table C E wf q z n ↔
    ∃ v, (C.encode v).length ≤ n ∧ v ≠ [] ∧ output C wf q z v ≠ C.encode v ∧
      a = C.encode v ∧ b = output C wf q z v := by
  classical
  simp only [table, List.mem_map, List.mem_filter, E.mem_words,
    decide_eq_true_eq, Prod.mk.injEq]
  aesop

theorem output_congr {u v : List A} (hq : q u = q v) : output C wf q z u = output C wf q z v := by
  simp only [output, hq, EncodedCanonical.least_congr C wf q hq]

theorem output_nil (hzero : q [] ≠ none) : output C wf q z [] = [] := by
  simp [output, hzero, EncodedCanonical.least_nil]

theorem whole_steps (hzero : q [] ≠ none) {n : ℕ} {v : List A} (hv : (C.encode v).length ≤ n) :
    Steps (table C E wf q z n) (C.encode v) (output C wf q z v) := by
  by_cases hn : v = []
  · subst v
    rw [C.encode_nil, output_nil C wf q z hzero]
  by_cases he : output C wf q z v = C.encode v
  · rw [he]
  · exact .single (by simpa using Step.apply ((mem_table C E wf q z).mpr
      ⟨v,hv,hn,he,rfl,rfl⟩) [] [])

def Contextual (n : ℕ) : Prop :=
  ∀ a b u v : List A, (C.encode (a++u++b)).length ≤ n →
    (C.encode (a++v++b)).length ≤ n → q u = q v → q (a++u++b) = q (a++v++b)

def ZeroIdeal (n : ℕ) : Prop :=
  ∀ a b u : List A, (C.encode (a++u++b)).length ≤ n → q u = none → q (a++u++b) = none

theorem branch_normalizes {n : ℕ} {rs : List (List S × List S)}
    (hzero : q [] ≠ none) (hz : Absorbs rs z)
    (ht : ∀ p ∈ table C E wf q z n, p ∈ rs)
    (hc : Contextual C q n) (hi : ZeroIdeal C q n)
    {v : List A} {a b : List A} (hlen : (C.encode (a++v++b)).length ≤ n) :
    Steps rs (C.encode a++output C wf q z v++C.encode b) (output C wf q z (a++v++b)) := by
  by_cases hq : q v = none
  · have hzq := hi a b v hlen hq
    simp only [output, ite_eq_left hq, ite_eq_left hzq]
    exact absorbs_context hz _ _
  · let v' := EncodedCanonical.least C wf q v
    have hlen' : (C.encode (a++v'++b)).length ≤ n := by
      have hh := EncodedCanonical.least_length C wf q v
      simp only [DelimiterCode.encode_append, List.length_append] at hlen ⊢
      dsimp only [v']
      omega
    have hqq : q (a++v'++b) = q (a++v++b) :=
      hc a b v' v hlen' hlen (EncodedCanonical.least_class C wf q v)
    have hh := steps_mono ht (whole_steps C E wf q z hzero hlen')
    rw [output_congr C wf q z hqq] at hh
    simpa only [output, ite_eq_right hq, DelimiterCode.encode_append, v'] using hh

theorem occurrence_normalizes {n : ℕ} {rs : List (List S × List S)}
    (hzero : q [] ≠ none) (hz : Absorbs rs z)
    (ht : ∀ p ∈ table C E wf q z n, p ∈ rs)
    (hc : Contextual C q n) (hi : ZeroIdeal C q n)
    {w v : List A} {x y : List S} (hw : (C.encode w).length ≤ n) (hv : v ≠ [])
    (he : C.encode w = x++C.encode v++y) :
    Steps rs (x++output C wf q z v++y) (output C wf q z w) := by
  obtain ⟨a,b,rfl,rfl,rfl⟩ := C.occurrence_decode hv he
  exact branch_normalizes C E wf q z hzero hz ht hc hi hw

theorem critical_containment {n k l : ℕ} {rs : List (List S × List S)}
    (hzero : q [] ≠ none) (hz : Absorbs rs z)
    (ht : ∀ p ∈ table C E wf q z n, p ∈ rs)
    (hc : Contextual C q n) (hi : ZeroIdeal C q n)
    {u u' v v' x y : List S}
    (hu : (u,u') ∈ table C E wf q z k) (hv : (v,v') ∈ table C E wf q z l)
    (he : u = x++v++y) (hlen : u.length ≤ n) :
    Join (Steps rs) u' (x++v'++y) := by
  obtain ⟨a,_,_,_,rfl,rfl⟩ := (mem_table C E wf q z).mp hu
  obtain ⟨b,_,hbn,_,rfl,rfl⟩ := (mem_table C E wf q z).mp hv
  exact ⟨output C wf q z a, .refl,
    occurrence_normalizes C E wf q z hzero hz ht hc hi hlen hbn he⟩

theorem critical_overlap {n k l : ℕ} {rs : List (List S × List S)}
    (hzero : q [] ≠ none) (hz : Absorbs rs z)
    (ht : ∀ p ∈ table C E wf q z n, p ∈ rs)
    (hc : Contextual C q n) (hi : ZeroIdeal C q n)
    {u u' v v' x middle y : List S}
    (hu : (u,u') ∈ table C E wf q z k) (hv : (v,v') ∈ table C E wf q z l)
    (hm : middle ≠ []) (he : u = x++middle) (hf : v = middle++y)
    (hlen : (x++middle++y).length ≤ n) :
    Join (Steps rs) (u'++y) (x++v') := by
  obtain ⟨a,_,_,_,rfl,rfl⟩ := (mem_table C E wf q z).mp hu
  obtain ⟨b,_,_,_,rfl,rfl⟩ := (mem_table C E wf q z).mp hv
  obtain ⟨c,d,e,rfl,rfl,rfl,rfl,rfl⟩ := C.overlap_decode hm he hf
  have hlen' : (C.encode (c++d++e)).length ≤ n := by
    simpa only [DelimiterCode.encode_append] using hlen
  refine ⟨output C wf q z (c++d++e), ?_, ?_⟩
  · simpa only [List.nil_append, DelimiterCode.encode_nil] using
      branch_normalizes C E wf q z hzero hz ht hc hi (a := []) (v := c++d) (b := e)
        (by simpa only [List.nil_append] using hlen')
  · simpa only [List.append_nil, DelimiterCode.encode_nil, List.append_assoc] using
      branch_normalizes C E wf q z hzero hz ht hc hi (a := c) (v := d++e) (b := [])
        (by simpa only [List.append_nil, List.append_assoc] using hlen')

theorem decreasing (n : ℕ) : ∀ p ∈ table C E wf q z n, List.Shortlex r p.2 p.1 := by
  intro ⟨u,v⟩ hp
  obtain ⟨w,_,hwn,hne,rfl,rfl⟩ := (mem_table C E wf q z).mp hp
  by_cases hz : q w = none
  · simp only [output, ite_eq_left hz]
    apply List.Shortlex.of_length_lt
    have hw := C.length_le_encode w
    have hp : 0 < w.length := List.length_pos_iff.mpr hwn
    simp only [List.length_singleton]
    omega
  · simp only [output, ite_eq_right hz] at hne ⊢
    rcases EncodedCanonical.least_lt_or_eq C wf q w with h | h
    · exact h
    · exact (hne (by rw [h])).elim

theorem stable {k n : ℕ} (hkn : k ≤ n) :
    Selectors.BoundedEq (table C E wf q z k) (table C E wf q z n) k := by
  intro ⟨u,v⟩ hlen
  rw [mem_table, mem_table]
  constructor
  · rintro ⟨w,hw,hn,he,rfl,rfl⟩
    exact ⟨w,hw.trans hkn,hn,he,rfl,rfl⟩
  · rintro ⟨w,hw,hn,he,rfl,rfl⟩
    exact ⟨w,hlen,hn,he,rfl,rfl⟩
end CodeTable
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
