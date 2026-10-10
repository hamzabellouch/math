import OAI.Computability.Superstring.Model

namespace OAI

namespace Superstring

namespace Hierarchical

variable {α : Type}


def SubstringClosed (V : Set (List α)) : Prop :=
  ∀ ⦃s⦄, s ∈ V → ∀ ⦃t⦄, t <:+: s → t ∈ V

/-- An explicit hierarchical-graph walk. Up edges append one symbol and down
edges delete the first symbol. Transitivity retains every edge of both walks. -/
inductive Path (V : Set (List α)) : List α → List α → Type
  | nil (s) (hs : s ∈ V) : Path V s s
  | up (s) (a) (hs : s ∈ V) (ht : s ++ [a] ∈ V) : Path V s (s ++ [a])
  | down (a) (s) (hs : a :: s ∈ V) (ht : s ∈ V) : Path V (a :: s) s
  | trans {s t u} : Path V s t → Path V t u → Path V s u

namespace Path

variable {V : Set (List α)} {s t u : List α}

def cost : {s t : List α} → Path V s t → ℕ
  | _, _, .nil _ _ => 0
  | _, _, .up _ _ _ _ => 1
  | _, _, .down _ _ _ _ => 0
  | _, _, .trans P Q => P.cost + Q.cost

/-- Vertices, including both endpoints, with no quotient of the edge data. -/
def Visits (w : List α) : {s t : List α} → Path V s t → Prop
  | _, _, .nil s _ => w = s
  | _, _, .up s a _ _ => w = s ∨ w = s ++ [a]
  | _, _, .down a s _ _ => w = a :: s ∨ w = s
  | _, _, .trans P Q => P.Visits w ∨ Q.Visits w

@[simp] theorem cost_trans (P : Path V s t) (Q : Path V t u) :
    (P.trans Q).cost = P.cost + Q.cost := rfl

@[simp] theorem visits_start (P : Path V s t) : P.Visits s := by
  induction P with
  | nil => rfl
  | up => exact Or.inl rfl
  | down => exact Or.inl rfl
  | trans P Q ih _ => exact Or.inl ih

@[simp] theorem visits_end (P : Path V s t) : P.Visits t := by
  induction P with
  | nil => rfl
  | up => exact Or.inr rfl
  | down => exact Or.inr rfl
  | trans P Q _ ih => exact Or.inr ih

theorem mem_of_visits (P : Path V s t) {w} (h : P.Visits w) : w ∈ V := by
  induction P with
  | nil s hs => exact h ▸ hs
  | up s a hs ht => rcases h with rfl | rfl <;> assumption
  | down a s hs ht => rcases h with rfl | rfl <;> assumption
  | trans P Q ihP ihQ => exact h.elim ihP ihQ

/-- Reindex an explicit walk along equality of its endpoint words. -/
def copy (P : Path V s t) {s' t' : List α} (hs : s = s') (ht : t = t') :
    Path V s' t' := hs ▸ ht ▸ P

@[simp] theorem cost_copy (P : Path V s t) {s' t' : List α}
    (hs : s = s') (ht : t = t') : (P.copy hs ht).cost = P.cost := by
  subst s'; subst t'; rfl

@[simp] theorem visits_copy (P : Path V s t) {s' t' : List α}
    (hs : s = s') (ht : t = t') (w : List α) : (P.copy hs ht).Visits w ↔ P.Visits w := by
  subst s'; subst t'; rfl

/-- Delete an arbitrary prefix, costing zero. -/
def deletePrefix (closed : SubstringClosed V) (a b : List α) (h : a ++ b ∈ V) :
    Path V (a ++ b) b :=
  match a with
  | [] => .nil b h
  | x :: xs =>
    let htail : xs ++ b ∈ V := closed h (List.infix_cons List.infix_rfl)
    (Path.down x (xs ++ b) h htail).trans (deletePrefix closed xs b htail)

@[simp] theorem cost_deletePrefix (closed : SubstringClosed V) (a b : List α)
    (h : a ++ b ∈ V) : (deletePrefix closed a b h).cost = 0 := by
  induction a with
  | nil => rfl
  | cons x xs ih => simpa [deletePrefix, cost] using ih _

/-- Append an arbitrary suffix, staying within prefixes of the final word. -/
def appendSuffix (closed : SubstringClosed V) (a b : List α) (h : a ++ b ∈ V) :
    Path V a (a ++ b) :=
  match b with
  | [] => (Path.nil a (by simpa using h)).copy rfl (by simp)
  | x :: xs =>
    let ha : a ∈ V := closed h List.infix_append_left
    let he : a ++ [x] ∈ V := closed h ⟨[], xs, by simp⟩
    let ht : (a ++ [x]) ++ xs ∈ V := by simpa using h
    ((Path.up a x ha he).trans (appendSuffix closed (a ++ [x]) xs ht)).copy rfl (by simp)

@[simp] theorem cost_appendSuffix (closed : SubstringClosed V) (a b : List α)
    (h : a ++ b ∈ V) : (appendSuffix closed a b h).cost = b.length := by
  induction b generalizing a with
  | nil => simp [appendSuffix, cost]
  | cons x xs ih => simp [appendSuffix, cost, ih, Nat.add_comm]

/-- A path that reads a word one letter at a time, always returning to empty.
This supplies the gap case of ordered windows without adding non-substring words. -/
def readGap (h0 : ([] : List α) ∈ V) (w : List α)
    (h : ∀ a ∈ w, [a] ∈ V) : Path V [] [] :=
  match w with
  | [] => .nil [] h0
  | a :: as =>
    ((Path.up [] a h0 (h a (by simp))).trans
      (Path.down a [] (h a (by simp)) h0)).trans
        (readGap h0 as (fun b hb => h b (by simp [hb])))

@[simp] theorem cost_readGap (h0 : ([] : List α) ∈ V) (w : List α)
    (h : ∀ a ∈ w, [a] ∈ V) : (readGap h0 w h).cost = w.length := by
  induction w with
  | nil => rfl
  | cons a as ih =>
    simp only [readGap, cost]
    rw [ih, List.length_cons]
    omega

end Path

/-- The finite integer window of a two-sided text. -/
def textWord (A : ℤ → α) (a b : ℤ) : List α :=
  List.ofFn (fun i : Fin (b - a).toNat => A (a + (i.val : ℤ)))

@[simp] theorem length_textWord (A : ℤ → α) (a b : ℤ) :
    (textWord A a b).length = (b - a).toNat := by
  simp [textWord]

@[simp] theorem textWord_self (A : ℤ → α) (a : ℤ) : textWord A a a = [] := by
  simp [textWord]

theorem textWord_append (A : ℤ → α) {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    textWord A a b ++ textWord A b c = textWord A a c := by
  apply List.ext_getElem
  · simp only [List.length_append, length_textWord]
    omega
  · intro i hi hj
    by_cases hit : i < (b - a).toNat
    · rw [List.getElem_append_left (by simpa using hit)]
      simp [textWord]
    · rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt hit)]
      simp only [textWord, List.getElem_ofFn, List.length_ofFn]
      congr 1
      omega

theorem textWord_infix (A : ℤ → α) {a b c d : ℤ}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    textWord A c d <:+: textWord A a b := by
  refine ⟨textWord A a c, textWord A d b, ?_⟩
  rw [textWord_append A hac hcd, textWord_append A (le_trans hac hcd) hdb]

theorem mem_textWord (A : ℤ → α) {a b : ℤ} {c : α} (hc : c ∈ textWord A a b) :
    ∃ i : ℤ, a ≤ i ∧ i < b ∧ A i = c := by
  simp only [textWord, List.mem_ofFn] at hc
  obtain ⟨i, hi⟩ := hc
  refine ⟨a + i.val, ?_, ?_, hi⟩ <;> omega

/-- Translate a window by a period of its text, preserving the graph vertex. -/
theorem textWord_translate (A : ℤ → α) (h : ℤ) (per : ∀ x, A (x + h) = A x)
    (a b : ℤ) : textWord A (a + h) (b + h) = textWord A a b := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [textWord, List.getElem_ofFn]
    rw [show a + h + (i : ℤ) = (a + i) + h by omega, per]


theorem ordered_windows {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V)
    {a b c d : ℤ} (_hab : a ≤ b) (hcd : c ≤ d) (hac : a ≤ c) (hbd : b ≤ d)
    (h₁ : textWord A a b ∈ V) (h₂ : textWord A c d ∈ V) :
    ∃ P : Path V (textWord A a b) (textWord A c d),
      P.cost = (d - b).toNat ∧
      ∃ w, P.Visits w ∧ (w.length : ℤ) ≤ max 0 (b - c) := by
  by_cases hcb : c ≤ b
  · have hm : textWord A c b ∈ V := closed h₁ (textWord_infix A hac hcb le_rfl)
    have heq₁ := textWord_append A hac hcb
    have heq₂ := textWord_append A hcb hbd
    have hd : textWord A a c ++ textWord A c b ∈ V := by simpa [heq₁] using h₁
    have hu : textWord A c b ++ textWord A b d ∈ V := by simpa [heq₂] using h₂
    let D := Path.deletePrefix closed (textWord A a c) (textWord A c b) hd
    let U := Path.appendSuffix closed (textWord A c b) (textWord A b d) hu
    have : ∃ P : Path V (textWord A a c ++ textWord A c b)
        (textWord A c b ++ textWord A b d),
        P.cost = (d - b).toNat ∧
        ∃ w, P.Visits w ∧ (w.length : ℤ) ≤ max 0 (b - c) := by
      refine ⟨D.trans U, ?_, textWord A c b, Or.inl (Path.visits_end D), ?_⟩
      · simp [D, U]
      · simp only [length_textWord]
        omega
    obtain ⟨P, hP, w, hw, hl⟩ := this
    exact ⟨P.copy heq₁ heq₂, by simpa using hP, w, by simpa using hw, hl⟩
  · have hbc : b ≤ c := by omega
    have h0 : ([] : List α) ∈ V := closed h₁ List.nil_infix
    let D := Path.deletePrefix closed (textWord A a b) [] (by simpa using h₁)
    let G := Path.readGap h0 (textWord A b c) (by
      intro x hx
      obtain ⟨i, _, _, rfl⟩ := mem_textWord A hx
      exact letters i)
    let U := Path.appendSuffix closed [] (textWord A c d) (by simpa using h₂)
    have : ∃ P : Path V (textWord A a b ++ []) ([] ++ textWord A c d),
        P.cost = (d - b).toNat ∧
        ∃ w, P.Visits w ∧ (w.length : ℤ) ≤ max 0 (b - c) := by
      refine ⟨(D.trans G).trans U, ?_, [], Or.inl (Or.inl (Path.visits_end D)), ?_⟩
      · simp only [Path.cost_trans, D, G, U, Path.cost_deletePrefix,
          Path.cost_readGap, Path.cost_appendSuffix, length_textWord]
        omega
      · simp
    obtain ⟨P, hP, w, hw, hl⟩ := this
    exact ⟨P.copy (by simp) (by simp), by simpa using hP, w, by simpa using hw, hl⟩


namespace Path

variable {V : Set (List α)}

theorem deletePrefix_visits (closed : SubstringClosed V) (a b c : List α)
    (h : (a ++ b) ++ c ∈ V) :
    (deletePrefix closed (a ++ b) c h).Visits (b ++ c) := by
  induction a with
  | nil => exact visits_start _
  | cons x xs ih =>
    exact Or.inr (ih _)

theorem appendSuffix_visits (closed : SubstringClosed V) (a b c : List α)
    (h : a ++ (b ++ c) ∈ V) :
    (appendSuffix closed a (b ++ c) h).Visits (a ++ b) := by
  induction b generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, appendSuffix, visits_copy, Visits]
    right
    simpa only [List.append_assoc, List.singleton_append] using ih (a ++ [x]) _

end Path

/-- Delete through a range of starting coordinates, visiting every suffix. -/
theorem window_delete {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) {a b c : ℤ} (hac : a ≤ c) (hcb : c ≤ b)
    (hw : textWord A a b ∈ V) :
    ∃ P : Path V (textWord A a b) (textWord A c b), P.cost = 0 ∧
      ∀ x, a ≤ x → x ≤ c → P.Visits (textWord A x b) := by
  have heq := textWord_append A hac hcb
  let D := Path.deletePrefix closed (textWord A a c) (textWord A c b) (heq.symm ▸ hw)
  refine ⟨D.copy heq rfl, by simp [D], ?_⟩
  intro x hax hxc
  simp only [Path.visits_copy]
  have heq' := textWord_append A hax hxc
  have hv := Path.deletePrefix_visits closed (textWord A a x) (textWord A x c)
    (textWord A c b) (show (textWord A a x ++ textWord A x c) ++ textWord A c b ∈ V by
      rw [heq', heq]; exact hw)
  dsimp [D]
  have hh : ∀ (a' : List α) (h : a' ++ textWord A c b ∈ V),
      a' = textWord A a c →
      (Path.deletePrefix closed a' (textWord A c b) h).Visits (textWord A x b) →
      (Path.deletePrefix closed (textWord A a c) (textWord A c b) (heq.symm ▸ hw)).Visits
        (textWord A x b) := by
    intro a' h e hv'; subst a'; exact hv'
  apply hh _ _ heq'
  simpa only [textWord_append A hxc hcb] using hv

/-- Append through a range of ends, visiting every prefix. -/
theorem window_append {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) {a b d : ℤ} (hab : a ≤ b) (hbd : b ≤ d)
    (hw : textWord A a d ∈ V) :
    ∃ P : Path V (textWord A a b) (textWord A a d),
      P.cost = (d - b).toNat ∧
      ∀ y, b ≤ y → y ≤ d → P.Visits (textWord A a y) := by
  have heq := textWord_append A hab hbd
  let U := Path.appendSuffix closed (textWord A a b) (textWord A b d) (heq.symm ▸ hw)
  refine ⟨U.copy rfl heq, by simp [U], ?_⟩
  intro y hby hyd
  simp only [Path.visits_copy]
  have heq' := textWord_append A hby hyd
  have hv := Path.appendSuffix_visits closed (textWord A a b) (textWord A b y)
    (textWord A y d) (show textWord A a b ++ (textWord A b y ++ textWord A y d) ∈ V by
      rw [heq', heq]; exact hw)
  have hh : ∀ (b' : List α) (h : textWord A a b ++ b' ∈ V),
      b' = textWord A b d →
      (Path.appendSuffix closed (textWord A a b) b' h).Visits (textWord A a y) →
      U.Visits (textWord A a y) := by
    intro b' h e hv'; subst b'; exact hv'
  apply hh _ _ heq'
  simpa only [textWord_append A hab hby] using hv

/-- An ordered-window transition can be chosen to contain every overlap suffix
up to its next start. This strengthens the contact assertion used for links. -/
theorem ordered_windows_suffixes {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V)
    {a b c d : ℤ} (hab : a ≤ b) (hcd : c ≤ d) (hac : a ≤ c) (hbd : b ≤ d)
    (h₁ : textWord A a b ∈ V) (h₂ : textWord A c d ∈ V) :
    ∃ P : Path V (textWord A a b) (textWord A c d),
      P.cost = (d - b).toNat ∧
      (∀ x, a ≤ x → x ≤ c → x ≤ b → P.Visits (textWord A x b)) ∧
      ∃ w, P.Visits w ∧ (w.length : ℤ) ≤ max 0 (b - c) := by
  let m := min b c
  have ham : a ≤ m := le_min hab hac
  have hmb : m ≤ b := min_le_left _ _
  obtain ⟨D, hDc, hDv⟩ := window_delete closed A ham hmb h₁
  have hmid : textWord A m b ∈ V := closed h₁ (textWord_infix A ham hmb le_rfl)
  obtain ⟨Q, hQc, w, hw, hl⟩ := ordered_windows closed A letters hmb hcd
    (min_le_right _ _) hbd hmid h₂
  refine ⟨D.trans Q, by simp [hDc, hQc], ?_, w, Or.inr hw, hl⟩
  intro x hax hxc hxb
  exact Or.inl (hDv x hax (le_min hxb hxc))


structure Layer (V : Set (List α)) (A : ℤ → α) (p : ℕ) where
  z : ℤ → ℤ
  mono : Monotone z
  lower : ∀ x, x ≤ z (x - 1)
  shift : ∀ x, z (x + p) = z x + p
  actual : ∀ x e, z (x - 1) ≤ e → e ≤ z x → textWord A x e ∈ V

namespace Layer

variable {V : Set (List α)} {A : ℤ → α} {p : ℕ}

def first (D : Layer V A p) (x : ℤ) : ℤ := D.z (x - 1)
def last (D : Layer V A p) (x : ℤ) : ℤ := D.z x

theorem first_le_last (D : Layer V A p) (x : ℤ) : D.first x ≤ D.last x :=
  D.mono (by omega)

theorem start_le_first (D : Layer V A p) (x : ℤ) : x ≤ D.first x := D.lower x

theorem first_actual (D : Layer V A p) (x : ℤ) : textWord A x (D.first x) ∈ V :=
  D.actual x _ le_rfl (D.first_le_last x)

theorem last_actual (D : Layer V A p) (x : ℤ) : textWord A x (D.last x) ∈ V :=
  D.actual x _ (D.first_le_last x) le_rfl

theorem shift_mul (D : Layer V A p) (k : ℕ) (x : ℤ) :
    D.z (x + (k * p : ℕ)) = D.z x + (k * p : ℕ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Nat.cast_add, ← add_assoc, D.shift, ih, add_assoc]

/-- An actual height crossing in any finite horizontal range. -/
theorem meets_height (D : Layer V A p) (a Y : ℤ) (K : ℕ)
    (hfirst : D.first a ≤ Y) (hlast : Y ≤ D.last (a + K)) :
    ∃ x : ℤ, a ≤ x ∧ x ≤ a + K ∧ D.first x ≤ Y ∧ Y ≤ D.last x := by
  let test : ℕ → Prop := fun n => n ≤ K ∧ Y ≤ D.z (a + n)
  have hex : ∃ n, test n := ⟨K, le_rfl, hlast⟩
  let n := Nat.find hex
  have hn : n ≤ K ∧ Y ≤ D.z (a + n) := Nat.find_spec hex
  refine ⟨a + n, by omega, by omega, ?_, hn.2⟩
  by_cases h0 : n = 0
  · simpa [h0] using hfirst
  · have hmin : ¬ test (n - 1) := Nat.find_min hex (by omega)
    have hz : D.z (a + ((n - 1 : ℕ) : ℤ)) < Y := by
      simp only [test, not_and, not_le] at hmin
      exact hmin (by omega)
    have heq : a + (n : ℤ) - 1 = a + ((n - 1 : ℕ) : ℤ) := by omega
    exact le_of_lt (by simpa [first, heq] using hz)


def TouchedBy (D : Layer V A p) {s t} (P : Path V s t) : Prop :=
  ∃ x e, D.first x ≤ e ∧ e ≤ D.last x ∧ P.Visits (textWord A x e)

end Layer

/-- Periods can be multiplied without assuming they are least. -/
theorem periodic_mul (A : ℤ → α) (p : ℕ) (per : ∀ x, A (x + p) = A x)
    (k : ℕ) (x : ℤ) : A (x + (k * p : ℕ)) = A x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Nat.cast_add, ← add_assoc, per, ih]


theorem collective_link {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (p k : ℕ)
    (per : ∀ x, A (x + p) = A x)
    {ι : Type} (L : ι → Layer V A p) (lo hi : ι)
    (hlo : ∀ i x, (L lo).z x ≤ (L i).z x)
    (hhi : ∀ i x, (L i).z x ≤ (L hi).z x)
    {a b : ℤ} (hab : a ≤ b) (hR : textWord A a b ∈ V)
    (h₁ : (L hi).first a ≤ b + (k * p : ℕ))
    (h₂ : (L hi).first a - (L lo).last a ≤ (k * p : ℕ))
    (h₃ : b ≤ (L lo).last a + (k * p : ℕ)) :
    ∃ P : Path V (textWord A a b) (textWord A a b),
      P.cost = k * p ∧ ∀ i, (L i).TouchedBy P := by
  let K : ℕ := k * p
  let Y := max b ((L hi).first a)
  have hbY : b ≤ Y := le_max_left _ _
  have hHY : (L hi).first a ≤ Y := le_max_right _ _
  have hYK : Y ≤ b + K := by dsimp [Y, K]; omega
  have haY : a ≤ Y := le_trans hab hbY
  have hYV : textWord A a Y ∈ V := by
    by_cases h : b ≤ (L hi).first a
    · simpa only [Y, max_eq_right h] using (L hi).first_actual a
    · simpa only [Y, max_eq_left (le_of_not_ge h)] using hR
  have perK : ∀ x, A (x + K) = A x := periodic_mul A p per k
  have heqR := textWord_translate A (K : ℤ) perK a b
  have hRV : textWord A (a + K) (b + K) ∈ V := heqR.symm ▸ hR
  obtain ⟨U, hUc, hUv⟩ := window_append closed A hab hbY hYV
  obtain ⟨Q, hQc, hQv, _⟩ := ordered_windows_suffixes closed A letters haY
    (show a + K ≤ b + K by omega) (show a ≤ a + K by omega) hYK hYV hRV
  refine ⟨(U.trans Q).copy rfl heqR, ?_, ?_⟩
  · simp only [Path.cost_copy, Path.cost_trans, hUc, hQc]
    dsimp [K] at *
    omega
  · intro i
    have hf : (L i).first a ≤ Y := le_trans (hhi i (a - 1)) hHY
    have hz : Y ≤ (L i).last (a + K) := by
      have heq := (L i).shift_mul k a
      have hlo' := hlo i a
      dsimp [Layer.last, K] at *
      rw [heq]
      dsimp [Y]
      omega
    obtain ⟨x, hax, hxK, hfx, hxl⟩ := (L i).meets_height a Y K hf hz
    refine ⟨x, Y, hfx, hxl, ?_⟩
    simp only [Path.visits_copy, Path.Visits]
    exact Or.inr (hQv x hax hxK (le_trans ((L i).start_le_first x) hfx))


theorem join_band {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (p k : ℕ)
    (per : ∀ x, A (x + p) = A x)
    {ι : Type} (L : ι → Layer V A p) (lo hi : ι)
    (hlo : ∀ i x, (L lo).z x ≤ (L i).z x)
    (hhi : ∀ i x, (L i).z x ≤ (L hi).z x)
    (t : ℤ) (hband : (L hi).first t - (L lo).last t ≤ (k * p : ℕ)) :
    ∃ P : Path V (textWord A t ((L lo).last t)) (textWord A t ((L lo).last t)),
      P.cost ≤ k * p ∧ ∀ i, (L i).TouchedBy P := by
  let E := (L lo).last t
  let H := (L hi).first t
  let K := k * p
  have hE : textWord A t E ∈ V := (L lo).last_actual t
  have hH : textWord A t H ∈ V := (L hi).first_actual t
  have htE : t ≤ E := le_trans ((L lo).start_le_first t) ((L lo).first_le_last t)
  have htH : t ≤ H := (L hi).start_le_first t
  by_cases hHE : H ≤ E
  · refine ⟨Path.nil _ hE, Nat.zero_le _, ?_⟩
    intro i
    refine ⟨t, E, le_trans (hhi i (t - 1)) hHE, hlo i t, rfl⟩
  · have hEH : E ≤ H := by omega
    have hHK : H ≤ E + K := by dsimp [H, E, K]; omega
    have perK : ∀ x, A (x + K) = A x := periodic_mul A p per k
    have heqE := textWord_translate A (K : ℤ) perK t E
    obtain ⟨U, hUc, hUv⟩ := window_append closed A htE hEH hH
    obtain ⟨Q, hQc, _⟩ := ordered_windows closed A letters htH
      (show t + K ≤ E + K by omega) (show t ≤ t + K by omega) hHK hH
      (heqE.symm ▸ hE)
    refine ⟨(U.trans Q).copy rfl heqE, ?_, ?_⟩
    · simp only [Path.cost_copy, Path.cost_trans, hUc, hQc]
      dsimp [K] at *
      omega
    · intro i
      let e := max E ((L i).first t)
      have hfe : (L i).first t ≤ e := le_max_right _ _
      have heE : E ≤ e := le_max_left _ _
      have hel : e ≤ (L i).last t := max_le (hlo i t) ((L i).first_le_last t)
      have heH : e ≤ H := max_le hEH (hhi i (t - 1))
      refine ⟨t, e, hfe, hel, ?_⟩
      simp only [Path.visits_copy, Path.Visits]
      exact Or.inl (hUv e heE heH)

/-- Forward rotations carry the usual lexicographic order, not a coordinatewise
order on streams. -/
def forward (A : ℤ → α) (t : ℤ) : Lex (ℕ → α) :=
  toLex (fun n => A (t + n))

theorem lex_at_le [LinearOrder α] {s t : Lex (ℕ → α)} (h : s ≤ t) (n : ℕ)
    (heq : ∀ j < n, s j = t j) : s n ≤ t n := by
  by_contra hn
  have hlt : t < s := ⟨n, fun j hj => (heq j hj).symm, lt_of_not_ge hn⟩
  exact (not_lt_of_ge h) hlt

/-- If a stream dominates its shift by q, then no smaller q-periodic stream
can have its first q letters. This is the first-difference argument in the
maximal-rotation lemma, expressed as strong induction. -/
theorem stream_eq_of_max [LinearOrder α] (s d : Lex (ℕ → α)) (q : ℕ)
    (hq : 0 < q) (hd : ∀ n, d (n + q) = d n)
    (hshift : toLex (fun n => s (n + q)) ≤ s) (hle : d ≤ s)
    (hprefix : ∀ n < q, s n = d n) : s = d := by
  apply funext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < q
    · exact hprefix n hn
    have hqn : q ≤ n := Nat.le_of_not_gt hn
    have hnq : n - q < n := by omega
    have heqn : n - q + q = n := Nat.sub_add_cancel hqn
    have hd' : d n = d (n - q) := by simpa only [heqn] using hd (n - q)
    have hsn : s n ≤ s (n - q) := by
      have hh := lex_at_le hshift (n - q) (fun j hj => ?_)
      · simpa only [Pi.toLex_apply, heqn] using hh
      · change s (j + q) = s j
        rw [ih (j + q) (by omega), hd j, ih j (by omega)]
    have hds : d n ≤ s n := lex_at_le hle n (fun j hj => (ih j hj).symm)
    apply le_antisymm _ hds
    rw [ih (n - q) hnq, ← hd'] at hsn
    exact hsn

/-- Integer periodic functions can be evaluated at their Euclidean residue. -/
theorem periodic_emod (A : ℤ → α) (p : ℤ) (per : ∀ x, A (x + p) = A x)
    (x : ℤ) : A (x % p) = A x := by
  have hp : Function.Periodic A p := per
  have h := hp.int_mul (x / p) (x % p)
  simpa only [Int.cast_id, Int.emod_add_ediv_mul] using h.symm

/-- Two periodic, two-sided texts are determined by their forward words. -/
theorem periodic_eq_of_forward_eq (A D : ℤ → α) (p q : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hA : ∀ x, A (x + p) = A x)
    (hD : ∀ x, D (x + q) = D x) (t : ℤ) (heq : forward A t = forward D t) :
    A = D := by
  have hAp := periodic_mul A p hA q
  have hDq := periodic_mul D q hD p
  have hc : (0 : ℤ) < p * q := by positivity
  have hAc : ∀ x, A (x + (p * q : ℤ)) = A x := by
    simpa only [Nat.cast_mul, mul_comm] using hAp
  have hDc : ∀ x, D (x + (p * q : ℤ)) = D x := by
    simpa only [Nat.cast_mul] using hDq
  funext x
  let r := (x - t) % (p * q : ℤ)
  have hr : 0 ≤ r := Int.emod_nonneg _ (ne_of_gt hc)
  have hperA : ∀ y, A (t + y + (p * q : ℤ)) = A (t + y) := fun y => hAc (t + y)
  have hperD : ∀ y, D (t + y + (p * q : ℤ)) = D (t + y) := fun y => hDc (t + y)
  have ha := periodic_emod (fun y => A (t + y)) (p * q) (by
    intro y; simpa only [add_assoc] using hperA y) (x - t)
  have hd := periodic_emod (fun y => D (t + y)) (p * q) (by
    intro y; simpa only [add_assoc] using hperD y) (x - t)
  simp only [add_sub_cancel] at ha hd
  rw [← ha, ← hd]
  have h := congrFun heq r.toNat
  simpa only [forward, Pi.toLex_apply, Int.toNat_of_nonneg hr] using h


theorem maximal_rotation [LinearOrder α] (A D : ℤ → α) (p q : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hA : ∀ x, A (x + p) = A x)
    (hD : ∀ x, D (x + q) = D x) (t : ℤ)
    (hmax : ∀ x, forward A x ≤ forward A t)
    (hbelow : ∀ x, forward D x ≤ forward A t) (hne : A ≠ D) :
    ∃ n < q, A (t + n) ≠ D (t + n) := by
  by_contra! h
  apply hne
  apply periodic_eq_of_forward_eq A D p q hp hq hA hD t
  apply stream_eq_of_max (forward A t) (forward D t) q hq
  · intro n
    simpa only [forward, Pi.toLex_apply, Nat.cast_add, add_assoc] using hD (t + n)
  · convert hmax (t + q) using 1
    congr 1
    funext n
    simp only [forward, Pi.toLex_apply]
    congr 1
    omega
  · exact hbelow t
  · exact h

/-- Agreement on the half-open integer interval [a,b). -/
def AgreeOn (A D : ℤ → α) (a b : ℤ) : Prop :=
  ∀ x, a ≤ x → x < b → A x = D x

theorem textWord_eq_of_agree {A D : ℤ → α} {a b : ℤ} (h : AgreeOn A D a b) :
    textWord A a b = textWord D a b := by
  apply congrArg List.ofFn
  funext i
  apply h
  · omega
  · have := i.isLt
    omega

theorem periodic_mod_at (A : ℤ → α) (p a x : ℤ)
    (per : ∀ y, A (y + p) = A y) : A (a + (x - a) % p) = A x := by
  have h := periodic_emod (fun y => A (a + y)) p (fun y => by
    simpa only [add_assoc] using per (a + y)) (x - a)
  simpa only [add_sub_cancel] using h

/-- Agreement for one period determines an aligned periodic text. -/
theorem same_period_eq (A D : ℤ → α) (p : ℕ) (hp : 0 < p)
    (hA : ∀ x, A (x + p) = A x) (hD : ∀ x, D (x + p) = D x)
    (a : ℤ) (h : AgreeOn A D a (a + p)) : A = D := by
  funext x
  rw [← periodic_mod_at A p a x hA, ← periodic_mod_at D p a x hD]
  apply h
  · have := Int.emod_nonneg (x - a) (show (p : ℤ) ≠ 0 by omega)
    omega
  · have := Int.emod_lt_of_pos (x - a) (show (0 : ℤ) < p by omega)
    omega


theorem eq_of_long_agreement (A D : ℤ → α) (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hA : ∀ x, A (x + p) = A x) (hD : ∀ x, D (x + q) = D x)
    (a : ℤ) (h : AgreeOn A D a (a + p + q)) : A = D := by
  have hDp : ∀ x, D (x + p) = D x := by
    intro x
    let y := a + (x - a) % (q : ℤ)
    have hay : a ≤ y := by
      have := Int.emod_nonneg (x - a) (show (q : ℤ) ≠ 0 by omega)
      dsimp [y]; omega
    have hyq : y < a + q := by
      have := Int.emod_lt_of_pos (x - a) (show (0 : ℤ) < q by omega)
      dsimp [y]; omega
    have hdyp : D (y + p) = D (x + p) :=
      periodic_mod_at (fun z => D (z + p)) q a x (fun z => by
        simpa only [add_right_comm] using hD (z + p))
    have hdy : D y = D x := periodic_mod_at D q a x hD
    rw [← hdyp, ← hdy, ← h (y + p) (by omega) (by omega),
      ← h y hay (by omega), hA y]
  apply same_period_eq A D p hp hA hDp a
  intro x hax hxb
  exact h x hax (by omega)

theorem agreement_bound (A D : ℤ → α) (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hA : ∀ x, A (x + p) = A x) (hD : ∀ x, D (x + q) = D x)
    (hne : A ≠ D) (a b : ℤ) (h : AgreeOn A D a b) : b - a < p + q := by
  by_contra hn
  apply hne
  apply eq_of_long_agreement A D p q hp hq hA hD a
  intro x hx hy
  exact h x hx (by omega)

theorem same_period_agreement_bound (A D : ℤ → α) (p : ℕ) (hp : 0 < p)
    (hA : ∀ x, A (x + p) = A x) (hD : ∀ x, D (x + p) = D x)
    (hne : A ≠ D) (a b : ℤ) (h : AgreeOn A D a b) : b - a < p := by
  by_contra hn
  apply hne
  apply same_period_eq A D p hp hA hD a
  intro x hx hy
  exact h x hx (by omega)

namespace Layer

variable {V : Set (List α)} {A : ℤ → α} {p : ℕ}

theorem first_mono (D : Layer V A p) : Monotone D.first :=
  fun _ _ h => D.mono (by omega)

theorem last_mono (D : Layer V A p) : Monotone D.last := D.mono

@[simp] theorem first_shift (D : Layer V A p) (x : ℤ) :
    D.first (x + p) = D.first x + p := by
  simpa only [first, add_sub_right_comm] using D.shift (x - 1)

@[simp] theorem last_shift (D : Layer V A p) (x : ℤ) :
    D.last (x + p) = D.last x + p := D.shift x

/-- An actual vertex of a layer whose symbol length is at most the allowance. -/
def HasShort (D : Layer V A p) (q : ℕ) : Prop :=
  ∃ x e, D.first x ≤ e ∧ e ≤ D.last x ∧ (textWord A x e).length ≤ q

theorem first_long_of_not_short (D : Layer V A p) (q : ℕ) (h : ¬ D.HasShort q)
    (x : ℤ) : (q : ℤ) < D.first x - x := by
  have hx : x ≤ D.first x := D.start_le_first x
  have hlen : ¬ (textWord A x (D.first x)).length ≤ q :=
    fun hc => h ⟨x, D.first x, le_rfl, D.first_le_last x, hc⟩
  simp only [length_textWord] at hlen
  omega

end Layer


theorem collective_short_sweep {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (p k q : ℕ)
    (hk : 1 ≤ k) (per : ∀ x, A (x + p) = A x)
    {ι : Type} (L : ι → Layer V A p) (hi : ι)
    (hhi : ∀ i x, (L i).z x ≤ (L hi).z x)
    (hlong : ∀ i, ¬ (L i).HasShort q)
    {a b t : ℤ} (hat : a ≤ t) (htb : t < b)
    (hR : textWord A a b ∈ V)
    (hH : (L hi).first t ≤ b + (k * p : ℕ))
    (hlen : b - a < p + q) (hagr : b - t < q) :
    ∃ P : Path V (textWord A a b) (textWord A a b),
      P.cost = k * p ∧ (∀ i, (L i).TouchedBy P) ∧
      ∃ w, P.Visits w ∧ w.length ≤ q := by
  let K := k * p
  let x := min t (a + K)
  let F := (L hi).first x
  have hpK : (p : ℤ) ≤ K := by
    have := Nat.mul_le_mul_right p hk
    simp only [one_mul] at this
    exact_mod_cast this
  have hax : a ≤ x := le_min hat (by omega)
  have hxt : x ≤ t := min_le_left _ _
  have hxK : x ≤ a + K := min_le_right _ _
  have hxb : x ≤ b := by omega
  have hshort : b - x < q := by
    by_cases h : t ≤ a + K
    · dsimp [x]; rw [min_eq_left h]; exact hagr
    · have heq : x = a + K := min_eq_right (by omega)
      rw [heq]
      omega
  have hbfirst : ∀ i, b ≤ (L i).first x := by
    intro i
    have := (L i).first_long_of_not_short q (hlong i) x
    omega
  have hbF : b ≤ F := hbfirst hi
  have hFK : F ≤ b + K := le_trans ((L hi).first_mono hxt) hH
  have hFV : textWord A x F ∈ V := (L hi).first_actual x
  have heqR := textWord_translate A (K : ℤ) (periodic_mul A p per k) a b
  obtain ⟨D, hDc, _⟩ := window_delete closed A hax hxb hR
  obtain ⟨U, hUc, hUv⟩ := window_append closed A hxb hbF hFV
  obtain ⟨Q, hQc, _⟩ := ordered_windows closed A letters (le_trans hxb hbF)
    (show a + K ≤ b + K by omega) hxK hFK hFV (heqR.symm ▸ hR)
  refine ⟨((D.trans U).trans Q).copy rfl heqR, ?_, ?_, ?_⟩
  · simp only [Path.cost_copy, Path.cost_trans, hDc, hUc, hQc]
    dsimp [K] at *
    omega
  · intro i
    refine ⟨x, (L i).first x, le_rfl, (L i).first_le_last x, ?_⟩
    simp only [Path.visits_copy, Path.Visits]
    exact Or.inl (Or.inr (hUv _ (hbfirst i) (hhi i (x - 1))))
  · refine ⟨textWord A x b, ?_, ?_⟩
    · simp only [Path.visits_copy, Path.Visits]
      exact Or.inl (Or.inl (Path.visits_end D))
    · simp only [length_textWord]
      omega


theorem cycle_collective_contact [LinearOrder α]
    {V : Set (List α)} (closed : SubstringClosed V)
    (A D : ℤ → α) (letters : ∀ x, [A x] ∈ V) (p k q : ℕ)
    (hp : 0 < p) (hk : 1 ≤ k) (hq : 0 < q)
    (per : ∀ x, A (x + p) = A x) (perD : ∀ x, D (x + q) = D x)
    {ι : Type} (L : ι → Layer V A p) (lo hi : ι)
    (hlo : ∀ i x, (L lo).z x ≤ (L i).z x)
    (hhi : ∀ i x, (L i).z x ≤ (L hi).z x)
    {a b t : ℤ} (hat : a ≤ t) (htb : t < b)
    (hR : textWord A a b ∈ V) (hagree : AgreeOn A D a b) (hne : A ≠ D)
    (hmax : ∀ x, forward A x ≤ forward A t)
    (hbelow : ∀ x, forward D x ≤ forward A t)
    (hH : (L hi).first t ≤ b + (k * p : ℕ))
    (hband : (L hi).first a - (L lo).last a ≤ (k * p : ℕ))
    (hlast : b ≤ (L lo).last a + (k * p : ℕ)) :
    ∃ P : Path V (textWord A a b) (textWord A a b),
      P.cost = k * p ∧ (∀ i, (L i).TouchedBy P) ∧
      ((∃ i, (L i).HasShort q) ∨ ∃ w, P.Visits w ∧ w.length ≤ q) := by
  classical
  by_cases hs : ∃ i, (L i).HasShort q
  · obtain ⟨P, hPc, hPv⟩ := collective_link closed A letters p k per L lo hi hlo hhi
      (show a ≤ b by omega) hR (le_trans ((L hi).first_mono hat) hH) hband hlast
    exact ⟨P, hPc, hPv, Or.inl hs⟩
  · have hlen := agreement_bound A D p q hp hq per perD hne a b hagree
    have hagr : b - t < q := by
      obtain ⟨n, hn, hne'⟩ := maximal_rotation A D p q hp hq per perD t hmax hbelow hne
      by_contra h
      exact hne' (hagree (t + n) (by omega) (by omega))
    obtain ⟨P, hPc, hPv, hc⟩ := collective_short_sweep closed A letters p k q hk per
      L hi hhi (by simpa only [not_exists] using hs) hat htb hR hH hlen hagr
    exact ⟨P, hPc, hPv, Or.inr hc⟩

namespace Path

variable {V : Set (List α)} {s t u : List α}

/-- The word written by a hierarchical walk: exactly one symbol per up edge. -/
def written : {s t : List α} → Path V s t → List α
  | _, _, .nil _ _ => []
  | _, _, .up _ a _ _ => [a]
  | _, _, .down _ _ _ _ => []
  | _, _, .trans P Q => P.written ++ Q.written

@[simp] theorem length_written (P : Path V s t) : P.written.length = P.cost := by
  induction P <;> simp_all [written, cost]

theorem end_suffix_written (P : Path V s t) : t <:+ s ++ P.written := by
  induction P with
  | nil => simp [written]
  | up => simp [written]
  | down a s _ _ => simp [written]
  | trans P Q ihP ihQ =>
    simpa only [written, List.append_assoc] using ihQ.trans (List.suffix_append_self_iff.mpr ihP)

/-- The exact output invariant in the main proof: every visited vertex occurs
contiguously in the starting word followed by the appended letters. -/
theorem visited_infix_written (P : Path V s t) {w : List α} (hw : P.Visits w) :
    w <:+: s ++ P.written := by
  induction P with
  | nil => subst w; simp [written]
  | up s a _ _ =>
    rcases hw with rfl | rfl
    · simpa only [written] using List.infix_append_left
    · simp [written]
  | down a s _ _ =>
    rcases hw with rfl | rfl
    · simp [written]
    · simp only [written, List.append_nil]
      exact List.infix_cons List.infix_rfl
  | trans P Q ihP ihQ =>
    rcases hw with hw | hw
    · simpa only [written, List.append_assoc] using
        (ihP hw).trans (List.infix_append_left (l₂ := Q.written))
    · have h := (List.suffix_append_self_iff.mpr (P.end_suffix_written) : _ ++ Q.written <:+ _).isInfix
      simpa only [written, List.append_assoc] using (ihQ hw).trans h

/-- Split at an actual visited vertex, preserving costs and every visit. -/
theorem split (P : Path V s t) {w : List α} (hw : P.Visits w) :
    ∃ (U : Path V s w) (D : Path V w t),
      U.cost + D.cost = P.cost ∧
      ∀ v, P.Visits v ↔ U.Visits v ∨ D.Visits v := by
  induction P with
  | nil s hs =>
    subst w
    exact ⟨.nil s hs, .nil s hs, rfl, fun _ => by simp [Visits]⟩
  | up s a hs ht =>
    rcases hw with h | h
    · subst w
      refine ⟨.nil s hs, .up s a hs ht, by simp [cost], ?_⟩
      intro v; simp only [Visits]; tauto
    · subst w
      refine ⟨.up s a hs ht, .nil (s ++ [a]) ht, by simp [cost], ?_⟩
      intro v; simp only [Visits]; tauto
  | down a s hs ht =>
    rcases hw with h | h
    · subst w
      refine ⟨.nil (a :: s) hs, .down a s hs ht, by simp [cost], ?_⟩
      intro v; simp only [Visits]; tauto
    · subst w
      refine ⟨.down a s hs ht, .nil s ht, by simp [cost], ?_⟩
      intro v; simp only [Visits]; tauto
  | trans P Q ihP ihQ =>
    rcases hw with hw | hw
    · obtain ⟨U, D, hc, hv⟩ := ihP hw
      refine ⟨U, D.trans Q, ?_, ?_⟩
      · simp only [cost_trans]; omega
      · intro v; simp only [Visits, hv, or_assoc]
    · obtain ⟨U, D, hc, hv⟩ := ihQ hw
      refine ⟨P.trans U, D, ?_, ?_⟩
      · simp only [cost_trans]; omega
      · intro v; simp only [Visits, hv, or_assoc]

/-- Rotate a closed walk to any of its visited vertices without adding edges. -/
theorem rotate (P : Path V s s) {w : List α} (hw : P.Visits w) :
    ∃ Q : Path V w w, Q.cost = P.cost ∧ ∀ v, Q.Visits v ↔ P.Visits v := by
  obtain ⟨U, D, hc, hv⟩ := P.split hw
  refine ⟨D.trans U, by simp only [cost_trans]; omega, ?_⟩
  intro v
  simp only [Visits, hv, or_comm]

/-- Euler splicing in its exact needed form: edge-disjointness is unnecessary
because edge copies remain distinct in the path data. -/
theorem splice (P : Path V s s) (Q : Path V t t) (w : List α)
    (hP : P.Visits w) (hQ : Q.Visits w) :
    ∃ R : Path V s s, R.cost = P.cost + Q.cost ∧
      ∀ v, R.Visits v ↔ P.Visits v ∨ Q.Visits v := by
  obtain ⟨U, D, hc, hv⟩ := P.split hP
  obtain ⟨Q', hQc, hQv⟩ := Q.rotate hQ
  refine ⟨(U.trans Q').trans D, ?_, ?_⟩
  · simp only [cost_trans]; omega
  · intro v
    simp only [Visits, hQv, hv]
    tauto

/-- Rooting at a short vertex costs exactly its symbol length. -/
theorem root_loop (closed : SubstringClosed V) (w : List α) (hw : w ∈ V) :
    ∃ P : Path V [] [], P.cost = w.length ∧ P.Visits w := by
  let U := (appendSuffix closed [] w (by simpa using hw))
  let D := (deletePrefix closed w [] (by simpa using hw))
  refine ⟨(U.copy (t' := w) rfl (by simp)).trans (D.copy (s' := w) (by simp) rfl), ?_, ?_⟩
  · simp [U, D]
  · exact Or.inl (visits_end _)

end Path

/-- Concatenate any finite ordered list of actual windows. -/
theorem ordered_chain {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V)
    (a b : ℕ → ℤ) (ha : Monotone a) (hb : Monotone b) (n : ℕ)
    (hab : ∀ i ≤ n, a i ≤ b i) (hV : ∀ i ≤ n, textWord A (a i) (b i) ∈ V) :
    ∃ P : Path V (textWord A (a 0) (b 0)) (textWord A (a n) (b n)),
      P.cost = (b n - b 0).toNat ∧
      ∀ i ≤ n, P.Visits (textWord A (a i) (b i)) := by
  induction n with
  | zero =>
    refine ⟨.nil _ (hV 0 le_rfl), by simp [Path.cost], ?_⟩
    intro i hi
    have : i = 0 := by omega
    subst i
    rfl
  | succ n ih =>
    obtain ⟨P, hPc, hPv⟩ := ih (fun i hi => hab i (by omega))
      (fun i hi => hV i (by omega))
    obtain ⟨Q, hQc, _⟩ := ordered_windows closed A letters (hab n (by omega))
      (hab (n + 1) le_rfl) (ha (by omega)) (hb (by omega))
      (hV n (by omega)) (hV (n + 1) le_rfl)
    refine ⟨P.trans Q, ?_, ?_⟩
    · simp only [Path.cost_trans, hPc, hQc]
      have := hb (show 0 ≤ n by omega)
      have := hb (show n ≤ n + 1 by omega)
      omega
    · intro i hi
      by_cases h : i ≤ n
      · exact Or.inl (hPv i h)
      · have : i = n + 1 := by omega
        subst i
        exact Or.inr (Path.visits_end Q)


theorem individual_link {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (p q : ℕ)
    (per : ∀ x, A (x + p) = A x) (L : Layer V A p)
    {a b : ℤ} (hab : a ≤ b) (hR : textWord A a b ∈ V)
    (hfirst : L.first a ≤ b) (hlast : b ≤ L.last a + p)
    (hlen : b - a < p + q) :
    ∃ P : Path V (textWord A a b) (textWord A a b),
      P.cost = p ∧ L.TouchedBy P ∧ ∃ w, P.Visits w ∧ w.length ≤ q := by
  let e := max b (L.first (a + p))
  have hbe : b ≤ e := le_max_left _ _
  have hfe : L.first (a + p) ≤ e := le_max_right _ _
  have heL : e ≤ L.last (a + p) := by
    apply max_le
    · simpa only [Layer.last_shift] using hlast
    · exact L.first_le_last _
  have hebp : e ≤ b + p := by
    apply max_le
    · omega
    · rw [Layer.first_shift]
      omega
  have hapse : a + p ≤ e := le_trans (L.start_le_first _) hfe
  have heV : textWord A (a + p) e ∈ V := L.actual _ _ hfe heL
  have heq := textWord_translate A p per a b
  obtain ⟨Q, hQc, w, hQw, hwlen⟩ := ordered_windows closed A letters hab hapse
    (by omega) hbe hR heV
  obtain ⟨U, hUc, _⟩ := window_append closed A hapse hebp (heq.symm ▸ hR)
  refine ⟨(Q.trans U).copy rfl heq, ?_, ?_, w, ?_, ?_⟩
  · simp only [Path.cost_copy, Path.cost_trans, hQc, hUc]
    omega
  · refine ⟨a + p, e, hfe, heL, ?_⟩
    simp only [Path.visits_copy, Path.Visits]
    exact Or.inl (Path.visits_end Q)
  · simpa only [Path.visits_copy, Path.Visits] using (Or.inl hQw : Q.Visits w ∨ U.Visits w)
  · omega


theorem one_free_period {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (p k : ℕ)
    (per : ∀ x, A (x + p) = A x)
    {ι : Type} (L : ι → Layer V A p) (lo hi : ι)
    (hlo : ∀ i x, (L lo).z x ≤ (L i).z x)
    (hhi : ∀ i x, (L i).z x ≤ (L hi).z x)
    (t : ℤ) (hband : (L hi).first t - (L lo).last t ≤ ((k - 1) * p : ℕ)) :
    ∃ P : Path V (textWord A t ((L lo).last t)) (textWord A t ((L lo).last t)),
      P.cost ≤ (k - 1) * p ∧ ∀ i, (L i).TouchedBy P :=
  join_band closed A letters p (k - 1) per L lo hi hlo hhi t hband

namespace Layer

variable {V : Set (List α)} {A : ℤ → α} {p : ℕ}

/-- Realize one entire vertical passage and its following down step. -/
theorem passage (L : Layer V A p) (closed : SubstringClosed V) (x : ℤ) :
    ∃ P : Path V (textWord A x (L.first x))
        (textWord A (x + 1) (L.first (x + 1))),
      P.cost = (L.first (x + 1) - L.first x).toNat ∧
      ∀ e, L.first x ≤ e → e ≤ L.last x → P.Visits (textWord A x e) := by
  have heq : L.first (x + 1) = L.last x := by simp [first, last]
  have hbound : x + 1 ≤ L.last x := by simpa only [heq] using L.start_le_first (x + 1)
  obtain ⟨U, hUc, hUv⟩ := window_append closed A (L.start_le_first x)
    (L.first_le_last x) (L.last_actual x)
  obtain ⟨D, hDc, _⟩ := window_delete closed A (show x ≤ x + 1 by omega)
    hbound (L.last_actual x)
  refine ⟨(U.trans D).copy rfl (by rw [heq]), ?_, ?_⟩
  · simp only [Path.cost_copy, Path.cost_trans, hUc, hDc, Nat.add_zero, heq]
  · intro e hfe hel
    simpa only [Path.visits_copy, Path.Visits] using
      (Or.inl (hUv e hfe hel) : U.Visits (textWord A x e) ∨ D.Visits (textWord A x e))

/-- A finite segment of a layer, including every window at its traversed starts. -/
theorem segment (L : Layer V A p) (closed : SubstringClosed V) (t : ℤ) (n : ℕ) :
    ∃ P : Path V (textWord A t (L.first t))
        (textWord A (t + n) (L.first (t + n))),
      P.cost = (L.first (t + n) - L.first t).toNat ∧
      ∀ x e, t ≤ x → x < t + n → L.first x ≤ e → e ≤ L.last x →
        P.Visits (textWord A x e) := by
  induction n with
  | zero =>
    refine ⟨(Path.nil _ (L.first_actual t)).copy rfl (by simp), by simp [Path.cost], ?_⟩
    intro x e htx hxt
    omega
  | succ n ih =>
    obtain ⟨P, hPc, hPv⟩ := ih
    obtain ⟨Q, hQc, hQv⟩ := L.passage closed (t + n)
    have hend : t + (n : ℤ) + 1 = t + (n + 1 : ℕ) := by omega
    refine ⟨(P.trans Q).copy rfl (by rw [hend]), ?_, ?_⟩
    · simp only [Path.cost_copy, Path.cost_trans, hPc, hQc]
      have h₁ := L.first_mono (show t ≤ t + (n : ℤ) by omega)
      have h₂ := L.first_mono (show t + (n : ℤ) ≤ t + n + 1 by omega)
      rw [hend] at *
      omega
    · intro x e htx hxt hfe hel
      simp only [Path.visits_copy, Path.Visits]
      by_cases h : x < t + n
      · exact Or.inl (hPv x e htx h hfe hel)
      · have hx : x = t + n := by omega
        subst x
        exact Or.inr (hQv e hfe hel)

/-- One primitive turn is an explicit closed walk of exactly the period cost. -/
theorem turn (L : Layer V A p) (closed : SubstringClosed V)
    (per : ∀ x, A (x + p) = A x) (t : ℤ) :
    ∃ P : Path V (textWord A t (L.first t)) (textWord A t (L.first t)),
      P.cost = p ∧
      ∀ x e, t ≤ x → x < t + p → L.first x ≤ e → e ≤ L.last x →
        P.Visits (textWord A x e) := by
  obtain ⟨P, hPc, hPv⟩ := L.segment closed t p
  have heq : textWord A (t + p) (L.first (t + p)) = textWord A t (L.first t) := by
    rw [L.first_shift]
    exact textWord_translate A p per t (L.first t)
  refine ⟨P.copy rfl heq, ?_, ?_⟩
  · simp only [Path.cost_copy, hPc, L.first_shift]
    omega
  · intro x e htx hxt hfe hel
    exact (Path.visits_copy ..).mpr (hPv x e htx hxt hfe hel)

end Layer

namespace Layer

variable {V : Set (List α)} {A : ℤ → α} {p : ℕ}

theorem shift_int (L : Layer V A p) (m x : ℤ) :
    L.z (x + m * p) = L.z x + m * p := by
  have h : Function.Periodic (fun y => L.z y - y) (p : ℤ) := by
    intro y
    change L.z (y + p) - (y + p) = L.z y - y
    rw [L.shift]
    omega
  have hh := h.int_mul m x
  simp only [Int.cast_id] at hh
  omega

theorem first_shift_int (L : Layer V A p) (m x : ℤ) :
    L.first (x + m * p) = L.first x + m * p := by
  simpa only [first, add_sub_right_comm] using L.shift_int m (x - 1)

/-- An entire layer is covered by one turn, because every actual window is a
period translate of a window in that turn. -/
theorem full_turn (L : Layer V A p) (closed : SubstringClosed V) (hp : 0 < p)
    (per : ∀ x, A (x + p) = A x) (t : ℤ) :
    ∃ P : Path V (textWord A t (L.first t)) (textWord A t (L.first t)),
      P.cost = p ∧ ∀ x e, L.first x ≤ e → e ≤ L.last x →
        P.Visits (textWord A x e) := by
  obtain ⟨P, hPc, hPv⟩ := L.turn closed per t
  refine ⟨P, hPc, ?_⟩
  intro x e hfe hel
  let r := t + (x - t) % (p : ℤ)
  let m := (x - t) / (p : ℤ)
  have htr : t ≤ r := by
    have := Int.emod_nonneg (x - t) (show (p : ℤ) ≠ 0 by omega)
    dsimp [r]; omega
  have hrt : r < t + p := by
    have := Int.emod_lt_of_pos (x - t) (show (0 : ℤ) < p by omega)
    dsimp [r]; omega
  have hrx : r + m * p = x := by
    have := Int.emod_add_ediv_mul (x - t) (p : ℤ)
    dsimp [r, m]; omega
  have hf : L.first r ≤ e - m * p := by
    have hh := L.first_shift_int m r
    rw [hrx] at hh
    omega
  have hl : e - m * p ≤ L.last r := by
    have hh := L.shift_int m r
    rw [hrx] at hh
    change e ≤ L.z x at hel
    change e - m * p ≤ L.z r
    omega
  have hpA : Function.Periodic A (p : ℤ) := per
  have heq := textWord_translate A (m * p) (hpA.int_mul m) r (e - m * p)
  rw [hrx, sub_add_cancel] at heq
  rw [heq]
  exact hPv r (e - m * p) htr hrt hf hl

end Layer

/-- A closed walk with its base vertex retained as explicit data. -/
structure Loop (V : Set (List α)) where
  base : List α
  path : Path V base base

namespace Loop

variable {V : Set (List α)}

def cost (P : Loop V) : ℕ := P.path.cost
def Visits (P : Loop V) (w : List α) : Prop := P.path.Visits w

def Meets (P Q : Loop V) : Prop := ∃ w, P.Visits w ∧ Q.Visits w

/-- Saturate a closed walk by splicing every accessible loop from a finite
collection. The resulting visited set is closed under that collection, and no
loop budget is spent twice. -/
theorem saturate {ι : Type} (F : ι → Loop V) (I : Finset ι) (P : Loop V) :
    ∃ Q : Loop V, Q.base = P.base ∧ Q.cost ≤ P.cost + ∑ i ∈ I, (F i).cost ∧
      (∀ w, P.Visits w → Q.Visits w) ∧
      (∀ i ∈ I, Q.Meets (F i) → ∀ w, (F i).Visits w → Q.Visits w) ∧
      (∀ w, Q.Visits w → P.Visits w ∨ ∃ i ∈ I, (F i).Visits w) := by
  classical
  induction I using Finset.strongInductionOn generalizing P
  rename_i I ih
  by_cases hex : ∃ i ∈ I, P.Meets (F i)
  · obtain ⟨i, hi, w, hPw, hFw⟩ := hex
    obtain ⟨R, hRc, hRv⟩ := P.path.splice (F i).path w hPw hFw
    let P' : Loop V := ⟨P.base, R⟩
    obtain ⟨Q, hQb, hQc, hPQ, hclosed, hsupport⟩ :=
      ih (I.erase i) (Finset.erase_ssubset hi) P'
    refine ⟨Q, hQb, ?_, ?_, ?_, ?_⟩
    · have hsum := Finset.sum_erase_add I (fun j => (F j).cost) hi
      change R.cost = P.cost + (F i).cost at hRc
      change Q.cost ≤ R.cost + _ at hQc
      omega
    · intro v hv
      apply hPQ v
      exact (hRv v).mpr (Or.inl hv)
    · intro j hj hmeet v hv
      by_cases hji : j = i
      · subst j
        apply hPQ v
        exact (hRv v).mpr (Or.inr hv)
      · exact hclosed j (Finset.mem_erase.mpr ⟨hji, hj⟩) hmeet v hv
    · intro v hv
      rcases hsupport v hv with h | ⟨j, hj, hv⟩
      · rcases (hRv v).mp h with hp | hf
        · exact Or.inl hp
        · exact Or.inr ⟨i, hi, hf⟩
      · exact Or.inr ⟨j, Finset.mem_of_mem_erase hj, hv⟩
  · refine ⟨P, rfl, Nat.le_add_right _ _, fun _ h => h, ?_, fun _ h => Or.inl h⟩
    intro i hi hmeet
    exact False.elim (hex ⟨i, hi, hmeet⟩)

/-- Used-support connectivity in a form that exactly expresses closure under
closed walks. It ignores incidental isolated vertices and records a root. -/
def Connected {ι : Type} (F : ι → Loop V) (I : Finset ι) (root : List α) : Prop :=
  ∀ U : Set (List α), root ∈ U →
    (∀ i ∈ I, (∃ w, w ∈ U ∧ (F i).Visits w) → ∀ w, (F i).Visits w → w ∈ U) →
    ∀ i ∈ I, ∀ w, (F i).Visits w → w ∈ U


theorem of_connected {ι : Type} (F : ι → Loop V) (I : Finset ι) (root : List α)
    (hroot : root ∈ V) (hconn : Connected F I root) :
    ∃ P : Path V root root, P.cost ≤ ∑ i ∈ I, (F i).cost ∧
      ∀ i ∈ I, ∀ w, (F i).Visits w → P.Visits w := by
  let P : Loop V := ⟨root, Path.nil root hroot⟩
  obtain ⟨Q, hQb, hQc, hPQ, hclosed, _⟩ := saturate F I P
  have hbase : Q.base = root := hQb
  refine ⟨Q.path.copy hbase hbase, ?_, ?_⟩
  · simpa only [Path.cost_copy, P, cost, Path.cost, Nat.zero_add] using hQc
  · have h := hconn {w | Q.Visits w} (hPQ root rfl) (fun i hi hmeet => hclosed i hi hmeet)
    intro i hi w hw
    exact (Path.visits_copy ..).mpr (h i hi w hw)

end Loop

/-- The host proof's modified target remains inside its recorded host window,
and lies within one child period of the prescribed requester window. -/
theorem host_target_bounds (a₀ b₀ a b e T : ℤ) (p₀ p : ℕ)
    (hmin : p₀ ≤ p) (horderA : a₀ ≤ a) (horderT : a ≤ T)
    (horderB : b₀ ≤ b)
    (hreq₁ : a + p < e) (hreq₂ : e ≤ b - p)
    (hleft : b₀ - a < p₀ + p) (hright : b - T < p + p₀)
    (hbase : b₀ < T + p₀) :
    let s := min (a + p) T
    let h := max e b₀
    a ≤ s ∧ s ≤ a + p ∧ s ≤ h ∧ h ≤ b ∧ e ≤ h ∧ h ≤ e + p ∧
      a₀ ≤ s ∧ s ≤ T ∧ b₀ ≤ h ∧ h < T + p₀ := by
  dsimp only
  have hs₁ : a ≤ min (a + p) T := le_min (by omega) horderT
  have hs₂ := min_le_left (a + (p : ℤ)) T
  have hs₃ := min_le_right (a + (p : ℤ)) T
  have hh₁ := le_max_left e b₀
  have hh₂ := le_max_right e b₀
  constructor
  · exact hs₁
  constructor
  · exact hs₂
  constructor
  · omega
  constructor
  · exact max_le (by omega) horderB
  constructor
  · exact hh₁
  constructor
  · exact max_le (by omega) (by omega)
  constructor
  · omega
  constructor
  · exact hs₃
  constructor
  · exact hh₂
  · exact max_lt (by omega) hbase

/-- The child-period loop used to attach each later requester at its modified
target; no recipient budget is consumed by this operation. -/
theorem request_attachment {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (p : ℕ)
    (per : ∀ x, A (x + p) = A x)
    {a e s h : ℤ} (hae : a ≤ e) (hsh : s ≤ h)
    (has : a ≤ s) (hsa : s ≤ a + p) (heh : e ≤ h) (hhe : h ≤ e + p)
    (hR : textWord A a e ∈ V) (hQ : textWord A s h ∈ V) :
    ∃ P : Path V (textWord A s h) (textWord A s h),
      P.cost = p ∧ P.Visits (textWord A a e) := by
  have heqR := textWord_translate A p per a e
  have heqQ := textWord_translate A p per s h
  obtain ⟨U, hUc, _⟩ := ordered_windows closed A letters hsh
    (show a + p ≤ e + p by omega) hsa hhe hQ (heqR.symm ▸ hR)
  obtain ⟨D, hDc, _⟩ := ordered_windows closed A letters
    (show a + p ≤ e + p by omega) (show s + p ≤ h + p by omega)
    (show a + p ≤ s + p by omega) (show e + p ≤ h + p by omega)
    (heqR.symm ▸ hR) (heqQ.symm ▸ hQ)
  refine ⟨(U.trans D).copy rfl heqQ, ?_, ?_⟩
  · simp only [Path.cost_copy, Path.cost_trans, hUc, hDc]
    omega
  · rw [← heqR]
    simp only [Path.visits_copy, Path.Visits]
    exact Or.inl (Path.visits_end U)

/-- The central cost-q excursion in the host text, for a nonempty ordered
list of later targets. It includes the initial requesters' whole vertical range
and ends with a contact shorter than the minimum child period. -/
theorem host_excursion {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (q p₀ : ℕ)
    (hp₀ : 0 < p₀) (per : ∀ x, A (x + q) = A x)
    (a₀ b₀ e₀ : ℤ) (he₀ : a₀ + p₀ < e₀) (heb : e₀ ≤ b₀)
    (hR : textWord A a₀ b₀ ∈ V)
    (s h : ℕ → ℤ) (hs : Monotone s) (hh : Monotone h) (n : ℕ)
    (hbounds : ∀ i ≤ n, a₀ ≤ s i ∧ s i ≤ a₀ + q ∧ s i ≤ h i ∧
      b₀ ≤ h i ∧ h i < a₀ + q + p₀)
    (hQ : ∀ i ≤ n, textWord A (s i) (h i) ∈ V) :
    ∃ P : Path V (textWord A a₀ e₀) (textWord A a₀ e₀),
      P.cost = q ∧ P.Visits (textWord A a₀ b₀) ∧
      (∀ e, e₀ ≤ e → e ≤ b₀ → P.Visits (textWord A a₀ e)) ∧
      (∀ i ≤ n, P.Visits (textWord A (s i) (h i))) ∧
      ∃ w, P.Visits w ∧ w.length < p₀ := by
  have hae : a₀ ≤ e₀ := by omega
  have hE : textWord A a₀ e₀ ∈ V := closed hR (textWord_infix A le_rfl hae heb)
  have heqE := textWord_translate A q per a₀ e₀
  obtain ⟨U, hUc, hUv⟩ := window_append closed A hae heb hR
  obtain ⟨B, hBc, _⟩ := ordered_windows closed A letters (le_trans hae heb)
    (hbounds 0 (by omega)).2.2.1 (hbounds 0 (by omega)).1
    (hbounds 0 (by omega)).2.2.2.1 hR (hQ 0 (by omega))
  obtain ⟨C, hCc, hCv⟩ := ordered_chain closed A letters s h hs hh n
    (fun i hi => (hbounds i hi).2.2.1) hQ
  obtain ⟨D, hDc, w, hDw, hwlen⟩ := ordered_windows closed A letters
    (hbounds n le_rfl).2.2.1 (show a₀ + q ≤ e₀ + q by omega)
    (hbounds n le_rfl).2.1 (show h n ≤ e₀ + q by
      have := (hbounds n le_rfl).2.2.2.2; omega) (hQ n le_rfl) (heqE.symm ▸ hE)
  refine ⟨(((U.trans B).trans C).trans D).copy rfl heqE, ?_, ?_, ?_, ?_, w, ?_, ?_⟩
  · simp only [Path.cost_copy, Path.cost_trans, hUc, hBc, hCc, hDc]
    have := hh (show 0 ≤ n by omega)
    have := (hbounds 0 (by omega)).2.2.2.1
    have := (hbounds n le_rfl).2.2.2.2
    omega
  · simp only [Path.visits_copy, Path.Visits]
    exact Or.inl (Or.inl (Or.inl (Path.visits_end U)))
  · intro e he he'
    simp only [Path.visits_copy, Path.Visits]
    exact Or.inl (Or.inl (Or.inl (hUv e he he')))
  · intro i hi
    simp only [Path.visits_copy, Path.Visits]
    exact Or.inl (Or.inr (hCv i hi))
  · simp only [Path.visits_copy, Path.Visits]
    exact Or.inr hDw
  · have := (hbounds n le_rfl).2.2.2.2
    omega

/-- The no-later-record case of the same host excursion. -/
theorem host_excursion_single {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (q p₀ : ℕ)
    (hp₀ : 0 < p₀) (per : ∀ x, A (x + q) = A x)
    (a₀ b₀ e₀ : ℤ) (he₀ : a₀ + p₀ < e₀) (heb : e₀ ≤ b₀)
    (hshort : b₀ < a₀ + q + p₀) (hR : textWord A a₀ b₀ ∈ V) :
    ∃ P : Path V (textWord A a₀ e₀) (textWord A a₀ e₀),
      P.cost = q ∧ P.Visits (textWord A a₀ b₀) ∧
      (∀ e, e₀ ≤ e → e ≤ b₀ → P.Visits (textWord A a₀ e)) ∧
      ∃ w, P.Visits w ∧ w.length < p₀ := by
  obtain ⟨P, hc, hr, hv, _, hs⟩ := host_excursion closed A letters q p₀ hp₀ per
    a₀ b₀ e₀ he₀ heb hR (fun _ => a₀) (fun _ => b₀)
    monotone_const monotone_const 0 (fun _ _ => ⟨le_rfl, by omega, by omega, le_rfl, hshort⟩)
    (fun _ _ => hR)
  exact ⟨P, hc, hr, hv, hs⟩

namespace Loop

variable {V : Set (List α)}

/-- Splice a family of request attachments into its host excursion. -/
theorem attach {ι : Type} (F : ι → Loop V) (I : Finset ι) (P : Loop V)
    (hmeet : ∀ i ∈ I, P.Meets (F i)) :
    ∃ Q : Loop V, Q.base = P.base ∧ Q.cost ≤ P.cost + ∑ i ∈ I, (F i).cost ∧
      (∀ w, P.Visits w → Q.Visits w) ∧
      (∀ i ∈ I, ∀ w, (F i).Visits w → Q.Visits w) := by
  obtain ⟨Q, hb, hc, hp, hclosed, _⟩ := saturate F I P
  refine ⟨Q, hb, hc, hp, ?_⟩
  intro i hi
  obtain ⟨w, hPw, hFw⟩ := hmeet i hi
  exact hclosed i hi ⟨w, hp w hPw, hFw⟩

/-- A short contact roots the whole closed excursion for its length. -/
theorem root_at (closed : SubstringClosed V) (P : Loop V) (w : List α)
    (hw : P.Visits w) :
    ∃ Q : Path V [] [], Q.cost = P.cost + w.length ∧
      ∀ v, P.Visits v → Q.Visits v := by
  obtain ⟨R, hRc, hRw⟩ := Path.root_loop closed w (P.path.mem_of_visits hw)
  obtain ⟨Q, hQc, hQv⟩ := R.splice P.path w hRw hw
  refine ⟨Q, ?_, fun v hv => (hQv v).mpr (Or.inr hv)⟩
  change Q.cost = R.cost + P.cost at hQc
  omega

/-- Host requests consume the host cost, the later attachments' costs, and
one unused minimum-child budget. The initial requesters remain visited. -/
theorem root_attachments {ι : Type} (closed : SubstringClosed V)
    (P : Loop V) (F : ι → Loop V) (I : Finset ι) (p₀ : ℕ)
    (hmeet : ∀ i ∈ I, P.Meets (F i))
    (hshort : ∃ w, P.Visits w ∧ w.length ≤ p₀) :
    ∃ Q : Path V [] [], Q.cost ≤ P.cost + (∑ i ∈ I, (F i).cost) + p₀ ∧
      (∀ w, P.Visits w → Q.Visits w) ∧
      (∀ i ∈ I, ∀ w, (F i).Visits w → Q.Visits w) := by
  obtain ⟨R, _, hRc, hp, hf⟩ := attach F I P hmeet
  obtain ⟨w, hw, hlen⟩ := hshort
  obtain ⟨Q, hQc, hQv⟩ := R.root_at closed w (hp w hw)
  exact ⟨Q, by omega, fun v hv => hQv v (hp v hv),
    fun i hi v hv => hQv v (hf i hi v hv)⟩

end Loop

end Hierarchical

end Superstring

end OAI
