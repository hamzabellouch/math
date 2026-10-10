import Mathlib
import OAI.GroupTheory.SimpleOvergroups.VariableCode

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding

namespace PaddedCode
section Syntax
variable {A : Type*} [Encodable A]

def body (cost : A → ℕ) (a : A) : List (Fin 4) :=
  List.replicate (Encodable.encode a) 0 ++ 1 :: List.replicate (10 * cost a) 0

def code (cost : A → ℕ) : DelimiterCode A (Fin 4) where
  start := 2
  stop := 3
  distinct := by decide
  body := body cost
  start_avoids := by intro a; simp [body]
  stop_avoids := by intro a; simp [body]
  injective := by
    intro a b he
    have hi (a : A) : (body cost a).idxOf 1 = Encodable.encode a := by
      rw [body, List.idxOf_append_of_notMem (by simp)]
      simp
    apply Encodable.encode_injective
    simpa only [hi] using congrArg (List.idxOf 1) he

@[simp] theorem block_length (cost : A → ℕ) (a : A) :
    ((code cost).block a).length = Encodable.encode a + 10 * cost a + 3 := by
  simp [DelimiterCode.block_length, code, body]
  omega

theorem descriptor_le_length (cost : A → ℕ) (a : A) :
    Encodable.encode a ≤ ((code cost).block a).length := by
  rw [block_length]; omega

theorem cost_padding (cost : A → ℕ) (a : A) :
    10 * cost a + 2 ≤ ((code cost).block a).length := by
  rw [block_length]; omega

def symbols (n : ℕ) : List A := (List.range (n + 1)).filterMap (Encodable.decode (α := A))

theorem mem_symbols_of_encode_le {a : A} {n : ℕ} (ha : Encodable.encode a ≤ n) :
    a ∈ symbols n := by
  apply List.mem_filterMap.mpr
  exact ⟨Encodable.encode a, List.mem_range.mpr (by omega), Encodable.encodek a⟩

def wordsOver (xs : List A) : ℕ → List (List A)
  | 0 => [[]]
  | n + 1 => [] :: xs.flatMap (fun a => (wordsOver xs n).map (a :: ·))

omit [Encodable A] in
@[simp] theorem mem_wordsOver [Encodable A] (xs : List A) (n : ℕ) (w : List A) :
    w ∈ wordsOver xs n ↔ w.length ≤ n ∧ ∀ a ∈ w, a ∈ xs := by
  induction n generalizing w with
  | zero =>
    cases w <;> simp [wordsOver]
  | succ n ih =>
    cases w with
    | nil => simp [wordsOver]
    | cons a w =>
      rw [wordsOver, List.mem_cons]
      constructor
      · rintro (he | h)
        · cases he
        · obtain ⟨b, hb, h⟩ := List.mem_flatMap.mp h
          obtain ⟨v, hv, he⟩ := List.mem_map.mp h
          obtain ⟨rfl, rfl⟩ := List.cons.inj he
          obtain ⟨hlen, hs⟩ := (ih v).mp hv
          exact ⟨by simpa using Nat.succ_le_succ hlen,
            by simpa [List.mem_cons] using And.intro hb hs⟩
      · rintro ⟨hlen, hs⟩
        right
        refine List.mem_flatMap.mpr ⟨a, hs a List.mem_cons_self,
          List.mem_map.mpr ⟨w, ?_, rfl⟩⟩
        exact (ih w).mpr ⟨by simpa using hlen,
          fun b hb => hs b (List.mem_cons_of_mem _ hb)⟩

omit [Encodable A] in
theorem block_length_le_encode [Encodable A] (C : DelimiterCode A (Fin 4)) {a : A} {w : List A}
    (ha : a ∈ w) : (C.block a).length ≤ (C.encode w).length := by
  induction w with
  | nil => simp at ha
  | cons b w ih =>
    simp only [DelimiterCode.encode_cons, List.length_append]
    rcases List.mem_cons.mp ha with rfl | ha
    · omega
    · have := ih ha; omega

def words (cost : A → ℕ) (n : ℕ) : List (List A) :=
  (wordsOver (symbols n) n).filter fun w => ((code cost).encode w).length ≤ n

@[simp] theorem mem_words (cost : A → ℕ) (n : ℕ) (w : List A) :
    w ∈ words cost n ↔ ((code cost).encode w).length ≤ n := by
  simp only [words, List.mem_filter, decide_eq_true_eq]
  refine ⟨And.right, fun hw => ⟨?_, hw⟩⟩
  apply (mem_wordsOver _ _ _).mpr
  refine ⟨?_, ?_⟩
  · have := (code cost).length_le_encode w
    omega
  · intro a ha
    exact mem_symbols_of_encode_le
      ((descriptor_le_length cost a).trans ((block_length_le_encode _ ha).trans hw))

theorem word_cost_bound (cost : A → ℕ) {n : ℕ} {w : List A}
    (hw : w ∈ words cost n) : DelimiterCode.cost cost w ≤ n / 10 :=
  (code cost).cost_le_quota cost (cost_padding cost) ((mem_words _ _ _).mp hw)

end Syntax

variable {A : Type*} [Primcodable A]

private theorem primrec_replicate (b : Fin 4) : Primrec (fun n => List.replicate n b) :=
  (Primrec.nat_rec₁ [] (Primrec.list_cons.comp (Primrec.const b) Primrec.snd).to₂).of_eq
    (by intro n; induction n <;> simp_all [List.replicate_succ])

theorem primrec_block (cost : A → ℕ) (hc : Primrec cost) :
    Primrec (code cost).block := by
  exact Primrec.list_cons.comp (Primrec.const 2)
    (Primrec.list_append.comp
      (Primrec.list_append.comp
        ((primrec_replicate 0).comp Primrec.encode)
        (Primrec.list_cons.comp (Primrec.const 1)
          ((primrec_replicate 0).comp
            (Primrec.nat_mul.comp (Primrec.const 10) hc))))
      (Primrec.const [3]))

theorem primrec_encode (cost : A → ℕ) (hc : Primrec cost) :
    Primrec (code cost).encode :=
  Primrec.list_flatMap Primrec.id ((primrec_block cost hc).comp Primrec.snd).to₂

theorem primrec_symbols : Primrec (@symbols A _) :=
  Primrec.listFilterMap (Primrec.list_range.comp Primrec.succ)
    (Primrec.decode.comp Primrec.snd).to₂

theorem primrec_wordsOver : Primrec₂ (@wordsOver A) := by
  exact (Primrec.nat_rec (Primrec.const [[]])
    (Primrec.list_cons.comp (Primrec.const [])
      (Primrec.list_flatMap Primrec.fst
        (Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂)).to₂).of_eq
            fun ls n => by induction n <;> simp_all [wordsOver]

theorem primrec_words (cost : A → ℕ) (hc : Primrec cost) : Primrec (words cost) := by
  have hfilter : Primrec (fun n => (wordsOver (symbols n) n).filterMap
      (fun w => if ((code cost).encode w).length ≤ n then some w else none)) :=
    Primrec.listFilterMap (primrec_wordsOver.comp primrec_symbols Primrec.id)
      (Primrec.ite (Primrec.nat_le.comp
        (Primrec.list_length.comp ((primrec_encode cost hc).comp Primrec.snd))
        Primrec.fst) (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).to₂
  apply hfilter.of_eq
  intro n
  simp only [words, ← List.filterMap_eq_filter, Option.guard, decide_eq_true_eq]

end PaddedCode
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
