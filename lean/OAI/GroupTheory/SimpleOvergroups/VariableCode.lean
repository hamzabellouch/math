import Mathlib
import OAI.GroupTheory.FiniteType.ProductGroupHomology

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding

structure DelimiterCode (A S : Type*) where
  start : S
  stop : S
  distinct : start ≠ stop
  body : A → List S
  start_avoids : ∀ a, start ∉ body a
  stop_avoids : ∀ a, stop ∉ body a
  injective : Function.Injective body

namespace DelimiterCode
variable {A S : Type*} (C : DelimiterCode A S)

def block (a : A) : List S := C.start :: (C.body a ++ [C.stop])
def encode (w : List A) : List S := w.flatMap C.block

@[simp] theorem block_length (a : A) : (C.block a).length = (C.body a).length + 2 := by
  simp [block]
@[simp] theorem encode_nil : C.encode [] = [] := rfl
@[simp] theorem encode_cons (a : A) (w : List A) :
    C.encode (a :: w) = C.block a ++ C.encode w := rfl
@[simp] theorem encode_append (u v : List A) :
    C.encode (u ++ v) = C.encode u ++ C.encode v := by simp [encode]

theorem length_le_encode (w : List A) : 2 * w.length ≤ (C.encode w).length := by
  induction w with
  | nil => simp
  | cons a w ih => simp only [encode_cons, List.length_append, block_length, List.length_cons]; omega

@[simp] theorem encode_eq_nil (w : List A) : C.encode w = [] ↔ w = [] := by
  constructor
  · intro h
    have := C.length_le_encode w
    simp only [h, List.length_nil] at this
    simpa using (show w.length = 0 by omega)
  · rintro rfl; rfl

theorem split_at_stop {t : S} {a b u v : List S} (ha : t ∉ a) (hb : t ∉ b)
    (he : a ++ t :: u = b ++ t :: v) : a = b ∧ u = v := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => exact ⟨rfl, (List.cons.inj he).2⟩
    | cons x b =>
      have hx := (List.cons.inj he).1
      exact (hb (by simp [hx])).elim
  | cons x a ih =>
    cases b with
    | nil =>
      have hx := (List.cons.inj he).1
      exact (ha (by simp [hx])).elim
    | cons y b =>
      obtain ⟨rfl, htail⟩ := List.cons.inj he
      obtain ⟨rfl, rfl⟩ := ih
        (fun h => ha (List.mem_cons_of_mem _ h))
        (fun h => hb (List.mem_cons_of_mem _ h)) htail
      exact ⟨rfl, rfl⟩

theorem block_cancel {a b : A} {u v : List S}
    (he : C.block a ++ u = C.block b ++ v) : a = b ∧ u = v := by
  simp only [block, List.cons_append, List.append_assoc] at he
  obtain ⟨hab, huv⟩ := split_at_stop (C.stop_avoids a) (C.stop_avoids b)
    (List.cons.inj he).2
  exact ⟨C.injective hab, huv⟩

theorem prefix_decode {u v : List A} {y : List S}
    (h : C.encode v = C.encode u ++ y) : ∃ w, v = u ++ w ∧ y = C.encode w := by
  induction u generalizing v with
  | nil => exact ⟨v, rfl, h.symm⟩
  | cons a u ih =>
    cases v with
    | nil => simp [block] at h
    | cons b v =>
      simp only [encode_cons, List.append_assoc] at h
      obtain ⟨rfl, ht⟩ := C.block_cancel h
      obtain ⟨w, rfl, rfl⟩ := ih ht
      exact ⟨w, rfl, rfl⟩

theorem encode_injective : Function.Injective C.encode := by
  intro u v h
  obtain ⟨w, hu, hw⟩ := C.prefix_decode (y := []) (by simpa using h)
  have hw : w = [] := (C.encode_eq_nil w).mp hw.symm
  simpa only [hw, List.append_nil] using hu

private theorem split_past_avoiding {b : S} {t z x y : List S} (ht : b ∉ t)
    (h : t ++ z = x ++ b :: y) : ∃ x', x = t ++ x' ∧ z = x' ++ b :: y := by
  induction t generalizing x with
  | nil => exact ⟨x, rfl, h⟩
  | cons a t ih =>
    cases x with
    | nil =>
      have ha : a = b := (List.cons.inj h).1
      exact (ht (by simp [ha])).elim
    | cons c x =>
      obtain ⟨rfl, htail⟩ := List.cons.inj h
      obtain ⟨x', rfl, hz⟩ := ih (fun hh => ht (List.mem_cons_of_mem _ hh)) htail
      exact ⟨x', rfl, hz⟩

private theorem tail_avoids (a : A) : C.start ∉ C.body a ++ [C.stop] := by
  simp [C.start_avoids, C.distinct]

theorem marker_alignment {v : List A} {x y : List S}
    (h : C.encode v = x ++ C.start :: y) :
    ∃ u a w, v = u ++ a :: w ∧ x = C.encode u ∧
      y = C.body a ++ C.stop :: C.encode w := by
  induction v generalizing x with
  | nil => simp at h
  | cons a v ih =>
    cases x with
    | nil =>
      have hy : (C.body a ++ [C.stop]) ++ C.encode v = y := (List.cons.inj h).2
      exact ⟨[], a, v, rfl, rfl, by simpa only [List.append_assoc, List.singleton_append] using hy.symm⟩
    | cons b x =>
      obtain ⟨rfl, hv⟩ := List.cons.inj h
      obtain ⟨x', rfl, hv'⟩ :=
        split_past_avoiding (C.tail_avoids a) hv
      obtain ⟨u, b, w, rfl, hx, hy⟩ := ih hv'
      exact ⟨a :: u, b, w, rfl, by simp [block, hx], hy⟩

theorem occurrence_decode {v u : List A} (hu : u ≠ []) {x y : List S}
    (h : C.encode v = x ++ C.encode u ++ y) :
    ∃ p q, v = p ++ u ++ q ∧ x = C.encode p ∧ y = C.encode q := by
  cases u with
  | nil => contradiction
  | cons a u =>
    have hm : C.encode v = x ++ C.start :: (C.body a ++ C.stop :: (C.encode u ++ y)) := by
      simpa [block, List.append_assoc] using h
    obtain ⟨p, b, w, hv, rfl, _⟩ := C.marker_alignment hm
    have hh : C.encode (b :: w) = C.encode (a :: u) ++ y := by
      apply List.append_cancel_left (as := C.encode p)
      simpa only [hv, encode_append, List.append_assoc] using h
    obtain ⟨q, hq, hqy⟩ := C.prefix_decode hh
    exact ⟨p, q, by rw [hv, hq, List.append_assoc], rfl, hqy⟩

theorem overlap_decode {u v : List A} {p middle q : List S}
    (hm : middle ≠ []) (h₁ : C.encode u = p ++ middle)
    (h₂ : C.encode v = middle ++ q) :
    ∃ a b c, u = a ++ b ∧ v = b ++ c ∧ p = C.encode a ∧
      middle = C.encode b ∧ q = C.encode c := by
  cases v with
  | nil => simp at h₂; exact (hm h₂.1).elim
  | cons v vs =>
    cases middle with
    | nil => contradiction
    | cons m middle =>
      have hm' : m = C.start := (List.cons.inj h₂).1.symm
      subst m
      obtain ⟨a, b, bs, hu, hp, ht⟩ := C.marker_alignment h₁
      have hs : C.start :: middle = C.encode (b :: bs) := by simp [block, ht]
      obtain ⟨c, hv, hq⟩ := C.prefix_decode (show
        C.encode (v :: vs) = C.encode (b :: bs) ++ q by simpa [hs] using h₂)
      exact ⟨a, b :: bs, c, hu, hv, hp, hs, hq⟩

theorem encode_avoids {s : S} (hs : s ≠ C.start) (ht : s ≠ C.stop)
    (hb : ∀ a, s ∉ C.body a) (u : List A) : s ∉ C.encode u := by
  simp only [encode, List.mem_flatMap, block, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false]
  rintro ⟨a, _, h | h | h⟩
  · exact hs h
  · exact hb a h
  · exact ht h

def cost (c : A → ℕ) (w : List A) : ℕ := (w.map c).sum
@[simp] theorem cost_nil (c : A → ℕ) : cost c [] = 0 := rfl
@[simp] theorem cost_cons (c : A → ℕ) (a : A) (w : List A) :
    cost c (a :: w) = c a + cost c w := rfl
@[simp] theorem cost_append (c : A → ℕ) (u v : List A) :
    cost c (u ++ v) = cost c u + cost c v := by simp [cost]

theorem cost_bound (c : A → ℕ)
    (hc : ∀ a, 10 * c a + 2 ≤ (C.block a).length) (w : List A) :
    10 * cost c w + 2 * w.length ≤ (C.encode w).length := by
  induction w with
  | nil => simp
  | cons a w ih =>
    have := hc a
    simp only [cost_cons, encode_cons, List.length_append, List.length_cons] at *
    omega

theorem cost_le_quota (c : A → ℕ)
    (hc : ∀ a, 10 * c a + 2 ≤ (C.block a).length)
    {w : List A} {n : ℕ} (hw : (C.encode w).length ≤ n) : cost c w ≤ n / 10 := by
  have := C.cost_bound c hc w
  omega

end DelimiterCode

theorem strict_dependency {n : ℕ} (hn : 0 < n) : 3 * (n / 10) < n := by omega

end SimpleFInftyOvergroups.ContextualEncoding

end OAI
