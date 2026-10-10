import OAI.Computability.Superstring.Periods

namespace OAI

namespace Superstring

namespace Counts.Data

variable {α : Type} [DecidableEq α] [Inhabited α]

/-- Prefix-subtree telescoping, stronger than the total-cost identity. -/
theorem down_descendants (D : Data α) (hD : D.WellFormed) {s : List α} (hs : s ≠ []) :
    (∑ r ∈ D.vertices with s <+: r, D.down r) = D.count s := by
  classical
  by_cases hsm : s ∈ D.vertices
  · let T := D.vertices.filter (fun r => s <+: r)
    have hsT : s ∈ T := Finset.mem_filter.mpr ⟨hsm, List.prefix_refl s⟩
    have hext : (∑ r ∈ T, ∑ c ∈ D.alphabet, D.count (r ++ [c])) =
        ∑ r ∈ T.erase s, D.count r := by
      rw [← Finset.sum_product T D.alphabet (fun a => D.count (a.1 ++ [a.2]))]
      apply Finset.sum_bij_ne_zero (fun a _ _ => a.1 ++ [a.2])
      · intro a ha hz
        obtain ⟨haT, _⟩ := Finset.mem_product.mp ha
        have hpre := (Finset.mem_filter.mp haT).2
        have hlen := hpre.length_le
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr
          ⟨D.mem_of_count_ne_zero hz, hpre.trans (List.prefix_append _ _)⟩⟩
        intro he
        have := congrArg List.length he
        simp only [List.length_append, List.length_singleton] at this
        omega
      · intro a _ _ b _ _ hab
        have he := congrArg List.dropLast hab
        simp only [List.dropLast_concat] at he
        have hc : a.2 = b.2 := by
          rw [he] at hab
          simpa only [List.append_cancel_left_eq, List.cons.injEq, and_true] using hab
        exact Prod.ext he hc
      · intro r hr hz
        obtain ⟨hrs, hrT⟩ := Finset.mem_erase.mp hr
        obtain ⟨hrV, hpre⟩ := Finset.mem_filter.mp hrT
        have hrne : r ≠ [] := by
          intro he
          have := hpre.length_le
          have hslen : 0 < s.length := List.length_pos_iff.mpr hs
          simp only [he, List.length_nil] at this
          omega
        have hsl : s.length < r.length := by
          have := hpre.length_le
          by_contra hn
          exact hrs (hpre.eq_of_length (by omega)).symm
        have hpl : s <+: r.dropLast :=
          List.prefix_of_prefix_length_le hpre (List.dropLast_prefix r)
            (by simp only [List.length_dropLast]; omega)
        have heq := List.dropLast_append_getLast hrne
        have hpT : r.dropLast ∈ T := Finset.mem_filter.mpr
          ⟨hD.closed hrV (List.dropLast_prefix r).isInfix, hpl⟩
        have hc : r.getLast hrne ∈ D.alphabet := hD.letters r hrV _
          (List.getLast_mem hrne)
        refine ⟨(r.dropLast, r.getLast hrne), Finset.mem_product.mpr ⟨hpT, hc⟩, ?_, heq⟩
        simpa only [heq] using hz
      · intros
        rfl
    have hadd := Finset.sum_congr rfl (fun r (hr : r ∈ T) =>
      D.down_add hD (s := r) (by
        intro he
        have hh := (Finset.mem_filter.mp hr).2.length_le
        have hslen : 0 < s.length := List.length_pos_iff.mpr hs
        simp only [he, List.length_nil] at hh
        omega))
    rw [Finset.sum_add_distrib, hext] at hadd
    have hsum := Finset.sum_erase_add T D.count hsT
    change (∑ r ∈ T, D.down r) = D.count s
    rw [← hsum] at hadd
    exact Nat.add_right_cancel (hadd.trans (Nat.add_comm _ _))
  · have he : D.vertices.filter (fun r => s <+: r) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      obtain ⟨hr, hp⟩ := Finset.mem_filter.mp hr
      exact hsm (hD.closed hr hp.isInfix)
    rw [he, Finset.sum_empty, D.count_zero s (Or.inl hsm)]

/-- Each copy of an actual base down edge is a distinct token. -/
abbrev DownToken (D : Data α) := Σ s : D.vertices, Fin (D.down s.val)

namespace DownToken

variable (D : Data α)

def word (i : D.DownToken) : List α := i.1.val

theorem mem (i : D.DownToken) : word D i ∈ D.vertices := i.1.property

theorem nonempty (i : D.DownToken) : word D i ≠ [] := by
  intro he
  have hi := i.2.isLt
  change i.2.val < D.down (word D i) at hi
  rw [he] at hi
  have hz := D.count_zero [] (Or.inr rfl)
  simp only [down, hz, Nat.zero_sub, Nat.not_lt_zero] at hi

theorem histogram (P : List α → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun i : D.DownToken => P (word D i))).card =
      ∑ s ∈ D.vertices, if P s then D.down s else 0 := by
  classical
  rw [Finset.card_filter, Fintype.sum_sigma]
  change (∑ x : D.vertices, ∑ _ : Fin (D.down x.val), if P x.val then 1 else 0) = _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_ite, mul_one, mul_zero]
  exact Finset.sum_coe_sort D.vertices (fun s => if P s then D.down s else 0)

theorem card (hD : D.WellFormed) : Fintype.card D.DownToken = D.weight := by
  have hh := histogram D (fun _ => True)
  simpa only [Finset.filter_true, Finset.card_univ, ite_true, D.total_down hD] using hh

theorem prefix_count (hD : D.WellFormed) {s : List α} (hs : s ≠ []) :
    (Finset.univ.filter (fun i : D.DownToken => s <+: word D i)).card = D.count s := by
  rw [histogram, ← Finset.sum_filter]
  exact D.down_descendants hD hs

/-- The capacity condition needed to thread the down tokens into passages. -/
theorem capacity (hD : D.WellFormed) (s : List α) :
    (Finset.univ.filter (fun i : D.DownToken => s <+: (word D i).tail)).card ≤
      (Finset.univ.filter (fun i : D.DownToken => s <+: word D i)).card := by
  classical
  by_cases hs : s = []
  · subst s
    simp only [List.nil_prefix, Finset.filter_true, le_refl]
  · let U := Finset.univ.filter (fun i : D.DownToken => s <+: (word D i).tail)
    have hf := Finset.sum_card_fiberwise_eq_card_filter U D.alphabet
      (fun i => (word D i).head (nonempty D i))
    have he : U.filter (fun i => (word D i).head (nonempty D i) ∈ D.alphabet) = U := by
      apply Finset.filter_eq_self.mpr
      intro i _
      exact hD.letters _ (mem D i) _ (List.head_mem (nonempty D i))
    rw [he] at hf
    have hterm (c : α) : U.filter (fun i => (word D i).head (nonempty D i) = c) =
        Finset.univ.filter (fun i : D.DownToken => c :: s <+: word D i) := by
      ext i
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
      have hpref (w : List α) (hn : w ≠ []) :
          (s <+: w.tail ∧ w.head hn = c) ↔ c :: s <+: w := by
        cases w with
        | nil => exact (hn rfl).elim
        | cons a w => simp only [List.tail_cons, List.head_cons, List.cons_prefix_cons]
                      tauto
      exact hpref _ (nonempty D i)
    simp_rw [hterm, prefix_count D hD (List.cons_ne_nil _ _)] at hf
    rw [prefix_count D hD hs]
    exact hf ▸ D.left_bound hD hs

end DownToken


theorem down_permutation (D : Data α) (hD : D.WellFormed) :
    ∃ f : Equiv.Perm D.DownToken,
      ∀ i, (DownToken.word D i).tail <+: DownToken.word D (f i) :=
  PrefixMatching.permutation _ _ (DownToken.capacity D hD)

end Counts.Data

namespace Hierarchical

variable {α ι : Type}

/-- Down-edge tokens threaded through the acyclic up-edge runs. -/
structure Threading (V : Set (List α)) (ι : Type) where
  word : ι → List α
  nonempty : ∀ i, word i ≠ []
  mem : ∀ i, word i ∈ V
  next : Equiv.Perm ι
  follows : ∀ i, (word i).tail <+: word (next i)

namespace Threading

variable {V : Set (List α)} (C : Threading V ι)

/-- The letter removed by the down step at each integer start coordinate. -/
def text (i : ι) (x : ℤ) : α :=
  (C.word ((C.next ^ x) i)).head (C.nonempty _)

theorem text_zpow (i : ι) (d x : ℤ) :
    C.text ((C.next ^ d) i) x = C.text i (x + d) := by
  simp only [text, zpow_add, Equiv.Perm.mul_apply]

theorem text_next (i : ι) (x : ℤ) : C.text (C.next i) x = C.text i (x + 1) := by
  simpa only [zpow_one] using C.text_zpow i 1 x

theorem text_period [Fintype ι] (i : ι) :
    Function.Periodic (C.text i) (orderOf C.next : ℤ) := by
  intro x
  rw [← C.text_zpow, zpow_natCast, pow_orderOf_eq_one]
  rfl

theorem exists_primitive_text [Fintype ι] (i : ι) :
    ∃ p, Primitive (C.text i) p :=
  exists_primitive (orderOf_pos C.next) (C.text_period i)

/-- Following tails proves that every old vertex is spelled by the infinite
text, even if it is longer than an entire turn of the threaded circulation. -/
theorem word_spelled (i : ι) :
    C.word i = textWord (C.text i) 0 (C.word i).length := by
  have hget : ∀ k (j : ι) (hk : k < (C.word j).length),
      (C.word j)[k] = C.text j (k : ℤ) := by
    intro k
    induction k with
    | zero =>
      intro j hk
      simp only [text, Nat.cast_zero, zpow_zero, Equiv.Perm.one_apply]
      exact (List.head_eq_getElem (C.nonempty j)).symm
    | succ k ih =>
      intro j hk
      have hkt : k < (C.word j).tail.length := by
        rw [List.length_tail]
        omega
      have hkn : k < (C.word (C.next j)).length :=
        lt_of_lt_of_le hkt (C.follows j).length_le
      calc
        (C.word j)[k + 1] = (C.word j).tail[k] := (List.getElem_tail hkt).symm
        _ = (C.word (C.next j))[k] := (C.follows j).getElem hkt
        _ = C.text (C.next j) (k : ℤ) := ih _ hkn
        _ = C.text j ((k + 1 : ℕ) : ℤ) := by
          simpa only [Nat.cast_add, Nat.cast_one] using C.text_next j (k : ℤ)
  apply List.ext_getElem
  · simp only [length_textWord, sub_zero, Int.toNat_natCast]
  · intro k hk hk'
    simp only [textWord, List.getElem_ofFn, zero_add]
    exact hget k i hk

/-- The actual exit vertex seen at any translated token. -/
theorem translated_word (i : ι) (x : ℤ) :
    C.word ((C.next ^ x) i) =
      textWord (C.text i) x (x + (C.word ((C.next ^ x) i)).length) := by
  calc
    C.word ((C.next ^ x) i) =
        textWord (C.text ((C.next ^ x) i)) 0 (C.word ((C.next ^ x) i)).length :=
      C.word_spelled _
    _ = textWord (C.text i) x (x + (C.word ((C.next ^ x) i)).length) := by
      apply List.ext_getElem
      · simp only [length_textWord, sub_zero, add_sub_cancel_left]
      · intro k hk hk'
        simp only [textWord, List.getElem_ofFn, zero_add, C.text_zpow]
        congr 1
        omega

/-- Entry-exit monotonicity before sorting; all entry windows are nonnegative. -/
theorem exit_mono_one (i : ι) :
    (C.word i).length ≤ 1 + (C.word (C.next i)).length := by
  have hh := (C.follows i).length_le
  rw [List.length_tail] at hh
  omega

end Threading

end Hierarchical

namespace Counts.Data

variable {α : Type} [DecidableEq α] [Inhabited α]

/-- Realize the base down multiset as a periodic circulation on actual vertices. -/
noncomputable def threading (D : Data α) (hD : D.WellFormed) :
    Hierarchical.Threading (D.vertices : Set (List α)) D.DownToken where
  word := DownToken.word D
  nonempty := DownToken.nonempty D
  mem := DownToken.mem D
  next := Classical.choose (D.down_permutation hD)
  follows := Classical.choose_spec (D.down_permutation hD)

end Counts.Data

namespace OrderStats

variable {β : Type} [LinearOrder β] {n : ℕ}

omit [LinearOrder β] in
theorem card_filter_perm (f : Fin n → β) (e : Equiv.Perm (Fin n))
    (P : β → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun i => P (f (e i)))).card =
      (Finset.univ.filter (fun i => P (f i))).card := by
  rw [Finset.card_filter, Finset.card_filter]
  exact Equiv.sum_comp e (fun i => if P (f i) then 1 else 0)

theorem order_perm (f : Fin n → β) (e : Equiv.Perm (Fin n)) (i : Fin n) :
    order (fun j => f (e j)) i = order f i :=
  order_eq_of_counts (fun t => card_filter_perm f e (fun v => v ≤ t)) i

end OrderStats

namespace Hierarchical.Threading

variable {α ι : Type} {V : Set (List α)} [Fintype ι]

/-- Tokens with a specified full-text alignment, not just a matching finite word. -/
def Aligned (C : Threading V ι) (A : ℤ → α) := {i : ι // C.text i = A}

noncomputable instance (C : Threading V ι) (A : ℤ → α) : Fintype (C.Aligned A) := by
  classical
  exact inferInstanceAs (Fintype {i : ι // C.text i = A})

noncomputable def enumerate (C : Threading V ι) (A : ℤ → α) :
    Fin (Fintype.card (C.Aligned A)) ≃ C.Aligned A := (Fintype.equivFin _).symm

/-- A text period permutes, rather than fixes, the multiple aligned passages. -/
def periodPerm (C : Threading V ι) {A : ℤ → α} {p : ℕ}
    (hp : Function.Periodic A (p : ℤ)) : Equiv.Perm (C.Aligned A) :=
  (C.next ^ (p : ℤ)).subtypeEquiv (by
    intro i
    constructor
    · intro hi
      funext x
      rw [C.text_zpow, hi]
      exact hp x
    · intro hi
      funext x
      have hh := congrFun hi (x - p)
      rw [C.text_zpow, sub_add_cancel] at hh
      exact hh.trans (by simpa only [sub_eq_add_neg] using hp.neg x))

/-- Exit ends of the unsorted primitive passages. -/
noncomputable def exits (C : Threading V ι) (A : ℤ → α) (x : ℤ)
    (j : Fin (Fintype.card (C.Aligned A))) : ℤ :=
  x + (C.word ((C.next ^ x) (C.enumerate A j).val)).length

theorem exits_step (C : Threading V ι) (A : ℤ → α) (x : ℤ)
    (j : Fin (Fintype.card (C.Aligned A))) : C.exits A x j ≤ C.exits A (x + 1) j := by
  have he : (C.next ^ (x + 1)) (C.enumerate A j).val =
      C.next ((C.next ^ x) (C.enumerate A j).val) := by
    rw [show x + 1 = 1 + x by omega, zpow_add, zpow_one, Equiv.Perm.mul_apply]
  have hh := C.exit_mono_one ((C.next ^ x) (C.enumerate A j).val)
  simp only [exits, he]
  omega

theorem exits_lower (C : Threading V ι) (A : ℤ → α) (x : ℤ)
    (j : Fin (Fintype.card (C.Aligned A))) : x + 1 ≤ C.exits A x j := by
  have hh := List.length_pos_iff.mpr (C.nonempty ((C.next ^ x) (C.enumerate A j).val))
  simp only [exits]
  omega

/-- Sorting independently at every coordinate gives the monotone layer function. -/
noncomputable def sortedExit (C : Threading V ι) (A : ℤ → α)
    (j : Fin (Fintype.card (C.Aligned A))) (x : ℤ) : ℤ := OrderStats.order (C.exits A x) j

theorem sortedExit_mono (C : Threading V ι) (A : ℤ → α)
    (j : Fin (Fintype.card (C.Aligned A))) : Monotone (C.sortedExit A j) := by
  apply monotone_int_of_le_succ
  intro x
  exact OrderStats.order_le_order (C.exits_step A x) j

theorem sortedExit_lower (C : Threading V ι) (A : ℤ → α)
    (j : Fin (Fintype.card (C.Aligned A))) (x : ℤ) : x ≤ C.sortedExit A j (x - 1) := by
  obtain ⟨k, hk⟩ := OrderStats.order_mem (C.exits A (x - 1)) j
  change x ≤ OrderStats.order (C.exits A (x - 1)) j
  rw [← hk]
  have := C.exits_lower A (x - 1) k
  omega

theorem exits_period (C : Threading V ι) {A : ℤ → α} {p : ℕ}
    (hp : Function.Periodic A (p : ℤ)) (x : ℤ)
    (j : Fin (Fintype.card (C.Aligned A))) :
    C.exits A (x + p) j =
      C.exits A x ((C.enumerate A).symm (C.periodPerm hp (C.enumerate A j))) + p := by
  have he : (C.periodPerm hp (C.enumerate A j)).val =
      (C.next ^ (p : ℤ)) (C.enumerate A j).val := rfl
  simp only [exits, Equiv.apply_symm_apply, he, zpow_add, Equiv.Perm.mul_apply]
  omega

theorem sortedExit_shift (C : Threading V ι) {A : ℤ → α} {p : ℕ}
    (hp : Function.Periodic A (p : ℤ))
    (j : Fin (Fintype.card (C.Aligned A))) (x : ℤ) :
    C.sortedExit A j (x + p) = C.sortedExit A j x + p := by
  let e : Equiv.Perm (Fin (Fintype.card (C.Aligned A))) :=
    (C.enumerate A).trans ((C.periodPerm hp).trans (C.enumerate A).symm)
  have he : C.exits A (x + p) = fun k => C.exits A x (e k) + p := by
    funext k
    exact C.exits_period hp x k
  change OrderStats.order (C.exits A (x + p)) j =
    OrderStats.order (C.exits A x) j + (p : ℤ)
  rw [he, OrderStats.order_add, OrderStats.order_perm]

theorem exits_actual (C : Threading V ι) (A : ℤ → α) (x : ℤ)
    (j : Fin (Fintype.card (C.Aligned A))) : textWord A x (C.exits A x j) ∈ V := by
  have he := C.translated_word (C.enumerate A j).val x
  rw [(C.enumerate A j).property] at he
  exact he ▸ C.mem ((C.next ^ x) (C.enumerate A j).val)

/-- The sorted windows are genuine substring vertices. No abstract completion of
V or artificial layer windows are introduced. -/
theorem sortedExit_actual (C : Threading V ι) (closed : SubstringClosed V)
    (A : ℤ → α) (j : Fin (Fintype.card (C.Aligned A))) (x e : ℤ)
    (hlo : C.sortedExit A j (x - 1) ≤ e) (hhi : e ≤ C.sortedExit A j x) :
    textWord A x e ∈ V := by
  obtain ⟨k, hk⟩ := OrderStats.order_mem (C.exits A x) j
  have hh : e ≤ C.exits A x k := by
    change e ≤ OrderStats.order (C.exits A x) j at hhi
    rwa [hk]
  exact closed (C.exits_actual A x k)
    (textWord_infix A le_rfl ((C.sortedExit_lower A j x).trans hlo) hh)

/-- The ordered-layer construction for a specified primitive-text group. -/
noncomputable def layer (C : Threading V ι) (closed : SubstringClosed V)
    {A : ℤ → α} {p : ℕ} (hp : Function.Periodic A (p : ℤ))
    (j : Fin (Fintype.card (C.Aligned A))) : Layer V A p where
  z := C.sortedExit A j
  mono := C.sortedExit_mono A j
  lower := C.sortedExit_lower A j
  shift := C.sortedExit_shift hp j
  actual := C.sortedExit_actual closed A j

theorem layers_ordered (C : Threading V ι) (A : ℤ → α)
    (i j : Fin (Fintype.card (C.Aligned A))) (hij : i ≤ j) (x : ℤ) :
    C.sortedExit A i x ≤ C.sortedExit A j x := OrderStats.monotone_order _ hij

/-- Exact conservation of vertical unit edges under the sorting operation. -/
theorem sorted_edges (C : Threading V ι) (A : ℤ → α) (x e : ℤ) :
    (Finset.univ.filter (fun j => C.sortedExit A j (x - 1) ≤ e ∧
      e < C.sortedExit A j x)).card =
    (Finset.univ.filter (fun j => C.exits A (x - 1) j ≤ e ∧
      e < C.exits A x j)).card := by
  apply OrderStats.sorted_edge_count
  intro j
  have hh := C.exits_step A (x - 1) j
  simpa only [sub_add_cancel] using hh

end Hierarchical.Threading

end Superstring

end OAI
