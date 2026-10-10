import Mathlib
import OAI.Combinatorics.HoneycombBridges.Basic

namespace OAI

/-! Bridge concatenation and single-crossing cuts. -/

noncomputable section
open scoped ENNReal
open Filter

namespace HoneycombActual

def shiftVertex (i j : ℤ) (v : Vertex) : Vertex :=
  ⟨v.col + i, v.row + j, v.up⟩

def concatenateVertices : List Bridge → List Vertex
  | [] => []
  | b :: bs => b.vertices ++
      (concatenateVertices bs).map (shiftVertex b.terminal b.height)

def BridgeFactorizationLaw : Prop :=
  ∀ b : Bridge, ∃! bs : List Bridge,
    (∀ a ∈ bs, a.Irreducible) ∧ concatenateVertices bs = b.vertices



@[simp] theorem shiftVertex_col (i j : ℤ) (v : Vertex) :
    (shiftVertex i j v).col = v.col + i := rfl
@[simp] theorem shiftVertex_row (i j : ℤ) (v : Vertex) :
    (shiftVertex i j v).row = v.row + j := rfl
@[simp] theorem shiftVertex_side (i j : ℤ) (v : Vertex) :
    (shiftVertex i j v).up = v.up := rfl
@[simp] theorem shiftVertex_up (i j a b : ℤ) :
    shiftVertex i j (up a b) = up (a+i) (b+j) := rfl
@[simp] theorem shiftVertex_down (i j a b : ℤ) :
    shiftVertex i j (down a b) = down (a+i) (b+j) := rfl
@[simp] theorem shiftVertex_zero (v : Vertex) : shiftVertex 0 0 v = v := by
  cases v; simp [shiftVertex]
@[simp] theorem shiftVertex_shift (i j k l : ℤ) (v : Vertex) :
    shiftVertex i j (shiftVertex k l v) = shiftVertex (k+i) (l+j) v := by
  cases v; simp [shiftVertex, add_assoc]

theorem shiftVertex_injective (i j : ℤ) : Function.Injective (shiftVertex i j) := by
  intro v w h
  have he := congrArg (shiftVertex (-i) (-j)) h
  simpa using he

@[simp] theorem shiftVertex_adj (i j : ℤ) (v w : Vertex) :
    Adj (shiftVertex i j v) (shiftVertex i j w) ↔ Adj v w := by
  simp only [Adj, UpDownAdj, shiftVertex_col, shiftVertex_row, shiftVertex_side]
  constructor <;> intro h <;> rcases h with ⟨hv, hw, h⟩ | ⟨hw, hv, h⟩
  · left; refine ⟨hv, hw, ?_⟩; omega
  · right; refine ⟨hw, hv, ?_⟩; omega
  · left; refine ⟨hv, hw, ?_⟩; omega
  · right; refine ⟨hw, hv, ?_⟩; omega

namespace Bridge

theorem vertices_ne_nil (b : Bridge) : b.vertices ≠ [] := by
  intro h
  have := b.initiates
  simp [h] at this

def concat (b c : Bridge) : Bridge where
  height := b.height + c.height
  terminal := b.terminal + c.terminal
  vertices := b.vertices ++ c.vertices.map (shiftVertex b.terminal b.height)
  height_pos := by have := b.height_pos; omega
  self_avoiding := by
    refine List.nodup_append.mpr ⟨b.self_avoiding,
      c.self_avoiding.map (shiftVertex_injective _ _), ?_⟩
    intro v hv w hw he
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hw
    have hv' := (b.in_strip v hv).2
    have hz' := (c.in_strip z hz).1
    have her := congrArg Vertex.row he
    simp only [shiftVertex_row] at her
    omega
  connected := by
    refine b.connected.append
      (List.isChain_map_of_isChain (shiftVertex b.terminal b.height)
        (fun v w h => (shiftVertex_adj _ _ _ _).mpr h) c.connected) ?_
    intro v hv w hw
    have hv' : v = down b.terminal ((b.height : ℤ)-1) := by
      symm; simpa [b.terminates] using hv
    have hw' : w = up b.terminal b.height := by
      symm; simpa [List.head?_map, c.initiates] using hw
    subst v; subst w
    simp [Adj, UpDownAdj, up, down]
  initiates := by simp [List.head?_append, b.initiates]
  terminates := by
    simp [List.getLast?_append, List.getLast?_map, c.terminates, b.terminates,
      sub_eq_add_neg, add_comm, add_assoc]
  in_strip := by
    intro v hv
    rcases List.mem_append.mp hv with hb | hc
    · have := b.in_strip v hb
      constructor
      · exact this.1
      · push_cast; have := c.height_pos; omega
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hc
      have := c.in_strip z hz
      simp only [shiftVertex_row, Nat.cast_add]
      constructor <;> omega

@[simp] theorem concat_vertices (b c : Bridge) :
    (b.concat c).vertices = b.vertices ++ c.vertices.map (shiftVertex b.terminal b.height) := rfl
@[simp] theorem concat_height (b c : Bridge) : (b.concat c).height = b.height + c.height := rfl
@[simp] theorem concat_terminal (b c : Bridge) : (b.concat c).terminal = b.terminal + c.terminal := rfl
@[simp] theorem concat_length (b c : Bridge) : (b.concat c).length = b.length + c.length := by
  simp [length]

theorem concat_assoc (a b c : Bridge) : (a.concat b).concat c = a.concat (b.concat c) := by
  apply vertices_injective
  simp only [concat_vertices, concat_height, concat_terminal, List.map_append, List.map_map,
    Function.comp_def, shiftVertex_shift, Nat.cast_add, List.append_assoc]
  congr 2
  apply List.map_congr_left
  intro v hv
  congr 1 <;> omega

end Bridge

@[simp] theorem weight_concat (b c : Bridge) : weight (b.concat c) = weight b * weight c := by
  simp only [weight, Bridge.concat_length, pow_add]
  exact ENNReal.ofReal_mul (pow_nonneg rho_pos.le _)

end HoneycombActual

namespace HoneycombActual.RenewalList

def changes {α : Type*} (q : α → Bool) (xs : List α) : ℕ :=
  (xs.zip xs.tail).countP (fun e => decide (q e.1 ≠ q e.2))

@[simp] theorem changes_nil {α : Type*} (q : α → Bool) : changes q [] = 0 := rfl
@[simp] theorem changes_singleton {α : Type*} (q : α → Bool) (x : α) :
    changes q [x] = 0 := rfl

@[simp] theorem changes_cons_cons {α : Type*} (q : α → Bool) (x y : α) (xs : List α) :
    changes q (x :: y :: xs) = changes q (y :: xs) + if q x = q y then 0 else 1 := by
  simp only [changes, List.tail_cons, List.zip_cons_cons, List.countP_cons]
  by_cases h : q x = q y <;> simp [h]

theorem constant_of_changes_zero {α : Type*} (q : α → Bool) (x : α) (xs : List α)
    (h : changes q (x :: xs) = 0) : ∀ y ∈ x :: xs, q y = q x := by
  induction xs generalizing x with
  | nil => simp
  | cons z xs ih =>
    rw [changes_cons_cons] at h
    have he : q x = q z := by split_ifs at h with he; omega
    have hz : changes q (z :: xs) = 0 := by simp [he] at h; exact h
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · rfl
    · exact (ih z hz y hy).trans he.symm

theorem split_of_changes_one {α : Type*} (q : α → Bool) (x : α) (xs : List α)
    (hx : q x = true) (h : changes q (x :: xs) = 1) :
    ∃ lo hi : List α, x :: xs = lo ++ hi ∧ lo ≠ [] ∧ hi ≠ [] ∧
      (∀ y ∈ lo, q y = true) ∧ (∀ y ∈ hi, q y = false) := by
  induction xs generalizing x with
  | nil => simp at h
  | cons z xs ih =>
    by_cases hz : q z = true
    · have hc : changes q (z :: xs) = 1 := by simpa [hx, hz] using h
      obtain ⟨lo, hi, he, hlo, hhi, hl, hu⟩ := ih z hz hc
      refine ⟨x :: lo, hi, by rw [he]; rfl, List.cons_ne_nil _ _, hhi, ?_, hu⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact hl y hy
    · have hz' : q z = false := Bool.eq_false_iff.mpr hz
      have hc : changes q (z :: xs) = 0 := by simpa [hx, hz'] using h
      refine ⟨[x], z :: xs, rfl, List.cons_ne_nil _ _, List.cons_ne_nil _ _, ?_, ?_⟩
      · intro y hy
        have : y = x := by simpa using hy
        simpa [this] using hx
      · intro y hy
        exact (constant_of_changes_zero q z xs hc y hy).trans hz'

end HoneycombActual.RenewalList

namespace HoneycombActual

def below (r : ℕ) (v : Vertex) : Bool := decide (v.row < (r : ℤ))

theorem crosses_eq_change (r : ℕ) (v w : Vertex) :
    Bridge.crosses r (v,w) = decide (below r v ≠ below r w) := by
  by_cases hv : v.row < (r : ℤ) <;> by_cases hw : w.row < (r : ℤ)
  all_goals simp [Bridge.crosses, below, hv, hw] <;> omega

theorem crossingCount_eq_changes (b : Bridge) (r : ℕ) :
    b.crossingCount r = RenewalList.changes (below r) b.vertices := by
  unfold Bridge.crossingCount RenewalList.changes
  congr 1
  funext e
  exact crosses_eq_change r e.1 e.2

theorem upward_crossing_shape (r : ℤ) {v w : Vertex}
    (ha : Adj v w) (hv : v.row < r) (hw : r ≤ w.row) :
    ∃ i : ℤ, v = down i (r-1) ∧ w = up i r := by
  rcases v with ⟨vc, vr, vu⟩
  rcases w with ⟨wc, wr, wu⟩
  simp only [Adj, UpDownAdj] at ha
  dsimp at ha hv hw
  rcases ha with ⟨hv', hw', hs⟩ | ⟨hw', hv', hs⟩
  · rcases hs with hs | hs | hs <;> omega
  · subst vu; subst wu
    rcases hs with ⟨hc, hr⟩ | ⟨hc, hr⟩ | ⟨hc, hr⟩
    · have he : vr = r-1 := by omega
      have he' : wr = r := by omega
      refine ⟨wc, ?_, ?_⟩ <;> simp [up, down, hc, he, he']
    · omega
    · omega

namespace Bridge

theorem split_at_of_crossingCount_one (b : Bridge) (r : ℕ)
    (hr : 0 < r) (hrb : r < b.height) (hc : b.crossingCount r = 1) :
    ∃ a c : Bridge, a.height = r ∧ b = a.concat c := by
  obtain ⟨xs, hxs⟩ := List.head?_eq_some_iff.mp b.initiates
  have hc' : RenewalList.changes (below r) (up 0 0 :: xs) = 1 := by
    simpa [crossingCount_eq_changes, hxs] using hc
  have hb : below r (up 0 0) = true := by simp [below, up]; omega
  obtain ⟨lo, hi, hlohi, hlo, hhi, hlow, hhigh⟩ :=
    RenewalList.split_of_changes_one (below r) (up 0 0) xs hb hc'
  have he : b.vertices = lo ++ hi := hxs.trans hlohi
  have hlo_sub (v : Vertex) (hv : v ∈ lo) : v ∈ b.vertices := by
    rw [he]; exact List.mem_append_left _ hv
  have hhi_sub (v : Vertex) (hv : v ∈ hi) : v ∈ b.vertices := by
    rw [he]; exact List.mem_append_right _ hv
  have hlr (v : Vertex) (hv : v ∈ lo) : v.row < (r : ℤ) := by
    simpa [below] using hlow v hv
  have hhr (v : Vertex) (hv : v ∈ hi) : (r : ℤ) ≤ v.row := by
    have := hhigh v hv
    simpa [below, not_lt] using this
  have hchain := List.isChain_append.mp (he ▸ b.connected)
  let v := lo.getLast hlo
  let w := hi.head hhi
  have hlv : lo.getLast? = some v := List.getLast?_eq_some_getLast hlo
  have hhw : hi.head? = some w := List.head?_eq_some_head hhi
  have hv : v ∈ lo := List.getLast_mem hlo
  have hw : w ∈ hi := List.head_mem hhi
  have hvw : Adj v w := hchain.2.2 v (by simp [hlv]) w (by simp [hhw])
  obtain ⟨i, hvi, hwi⟩ := upward_crossing_shape (r : ℤ) hvw (hlr v hv) (hhr w hw)
  have hn := List.nodup_append.mp (he ▸ b.self_avoiding)
  have hlhead : lo.head? = some (up 0 0) := by
    have := b.initiates
    rw [he, List.head?_append] at this
    cases hh : lo.head? with
    | none => exact False.elim (hlo (List.head?_eq_none_iff.mp hh))
    | some z => simpa [hh] using this
  have hhlast : hi.getLast? = some (down b.terminal ((b.height : ℤ)-1)) := by
    have := b.terminates
    rw [he, List.getLast?_append] at this
    cases hh : hi.getLast? with
    | none => exact False.elim (hhi (List.getLast?_eq_none_iff.mp hh))
    | some z => simpa [hh] using this
  let a : Bridge := {
    height := r
    terminal := i
    vertices := lo
    height_pos := hr
    self_avoiding := hn.1
    connected := hchain.1
    initiates := hlhead
    terminates := by simpa [hvi] using hlv
    in_strip := by
      intro z hz
      exact ⟨(b.in_strip z (hlo_sub z hz)).1, hlr z hz⟩ }
  let c : Bridge := {
    height := b.height - r
    terminal := b.terminal - i
    vertices := hi.map (shiftVertex (-i) (-(r : ℤ)))
    height_pos := by omega
    self_avoiding := hn.2.1.map (shiftVertex_injective _ _)
    connected := List.isChain_map_of_isChain _
      (fun z z' ha => (shiftVertex_adj _ _ _ _).mpr ha) hchain.2.1
    initiates := by simp [List.head?_map, hhw, hwi]
    terminates := by
      simp only [List.getLast?_map, hhlast, Option.map_some, shiftVertex_down,
        Nat.cast_sub hrb.le]
      congr 1; congr 1; omega
    in_strip := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      have hs := (b.in_strip y (hhi_sub y hy)).2
      have hr' := hhr y hy
      simp only [shiftVertex_row, Nat.cast_sub hrb.le]
      constructor <;> omega }
  refine ⟨a, c, rfl, ?_⟩
  apply vertices_injective
  simp only [concat_vertices]
  change b.vertices = lo ++ (hi.map (shiftVertex (-i) (-(r : ℤ)))).map (shiftVertex i r)
  simpa [List.map_map, Function.comp_def] using he

end Bridge
end HoneycombActual

namespace HoneycombActual.RenewalList

theorem changes_zero_of_constant {α : Type*} (q : α → Bool) (xs : List α) (a : Bool)
    (h : ∀ x ∈ xs, q x = a) : changes q xs = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      rw [changes_cons_cons, ih (by intro z hz; exact h z (List.mem_cons_of_mem _ hz))]
      simp [h x (by simp), h y (by simp)]

theorem changes_append {α : Type*} (q : α → Bool) (lo hi : List α) (v w : α)
    (hl : lo.getLast? = some v) (hh : hi.head? = some w) :
    changes q (lo ++ hi) = changes q lo + changes q hi + if q v = q w then 0 else 1 := by
  induction lo generalizing v with
  | nil => simp at hl
  | cons x xs ih =>
    cases xs with
    | nil =>
      have hx : x = v := by simpa using hl
      obtain ⟨ys, rfl⟩ := List.head?_eq_some_iff.mp hh
      simp [hx]
    | cons y ys =>
      have hl' : (y :: ys).getLast? = some v := by simpa using hl
      simp only [List.cons_append, changes_cons_cons]
      have hih := ih v hl'
      simp only [List.cons_append] at hih
      omega

theorem takeWhile_append_of_sides {α : Type*} (q : α → Bool) (lo hi : List α)
    (hl : ∀ x ∈ lo, q x = true) (hh : ∀ x ∈ hi, q x = false) :
    (lo ++ hi).takeWhile q = lo := by
  induction lo with
  | nil =>
    cases hi with
    | nil => rfl
    | cons y ys => simp [hh y (by simp)]
  | cons x xs ih =>
    simp only [List.cons_append, List.takeWhile_cons]
    rw [hl x (by simp)]
    simpa using congrArg (List.cons x)
      (ih (by intro y hy; exact hl y (List.mem_cons_of_mem _ hy)))

end HoneycombActual.RenewalList

namespace HoneycombActual.Bridge

@[simp] theorem concat_crossing_at (b c : Bridge) :
    (b.concat c).crossingCount b.height = 1 := by
  let hi := c.vertices.map (shiftVertex b.terminal b.height)
  have hl0 : RenewalList.changes (below b.height) b.vertices = 0 :=
    RenewalList.changes_zero_of_constant _ _ true (by
      intro v hv; simpa [below] using (b.in_strip v hv).2)
  have hh0 : RenewalList.changes (below b.height) hi = 0 :=
    RenewalList.changes_zero_of_constant _ _ false (by
      intro v hv
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
      have := (c.in_strip z hz).1
      simp [below]; omega)
  have hlast : below b.height (down b.terminal ((b.height : ℤ)-1)) = true := by
    simp [below, down]
  have hfirst : below b.height (up b.terminal b.height) = false := by simp [below, up]
  have hc := RenewalList.changes_append (below b.height) b.vertices hi
    (down b.terminal ((b.height : ℤ)-1)) (up b.terminal b.height)
    b.terminates (by simp [hi, List.head?_map, c.initiates])
  simpa [crossingCount_eq_changes, concat_vertices, hi, hl0, hh0, hlast, hfirst] using hc

theorem concat_crossing_below (b c : Bridge) (r : ℕ) (hr : r < b.height) :
    (b.concat c).crossingCount r = b.crossingCount r := by
  let hi := c.vertices.map (shiftVertex b.terminal b.height)
  have hh0 : RenewalList.changes (below r) hi = 0 :=
    RenewalList.changes_zero_of_constant _ _ false (by
      intro v hv
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
      have hz0 := (c.in_strip z hz).1
      change decide (z.row + (b.height : ℤ) < (r : ℤ)) = false
      simp only [decide_eq_false_iff_not, not_lt]
      omega)
  have hlast : below r (down b.terminal ((b.height : ℤ)-1)) = false := by
    simp [below, down]; omega
  have hfirst : below r (up b.terminal b.height) = false := by simp [below, up]; omega
  have hc := RenewalList.changes_append (below r) b.vertices hi
    (down b.terminal ((b.height : ℤ)-1)) (up b.terminal b.height)
    b.terminates (by simp [hi, List.head?_map, c.initiates])
  simpa [crossingCount_eq_changes, concat_vertices, hi, hh0, hlast, hfirst] using hc

theorem takeWhile_concat (b c : Bridge) :
    (b.concat c).vertices.takeWhile (below b.height) = b.vertices := by
  apply RenewalList.takeWhile_append_of_sides
  · intro v hv
    simpa [below] using (b.in_strip v hv).2
  · intro v hv
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
    have := (c.in_strip z hz).1
    simp [below]; omega

theorem concat_first_eq_of_height_eq {a b c d : Bridge}
    (he : a.concat b = c.concat d) (hh : a.height = c.height) : a = c := by
  apply vertices_injective
  calc
    a.vertices = (a.concat b).vertices.takeWhile (below a.height) := (takeWhile_concat _ _).symm
    _ = (c.concat d).vertices.takeWhile (below c.height) := by rw [he, hh]
    _ = c.vertices := takeWhile_concat _ _

theorem concat_left_cancel {a b c : Bridge} (he : a.concat b = a.concat c) : b = c := by
  apply vertices_injective
  have hv := congrArg Bridge.vertices he
  simp only [concat_vertices, List.append_cancel_left_eq] at hv
  have hi := congrArg (List.map (shiftVertex (-a.terminal) (-(a.height : ℤ)))) hv
  simpa [List.map_map, Function.comp_def] using hi

theorem concat_irreducible_first_height_eq {a b c d : Bridge}
    (ha : a.Irreducible) (hc : c.Irreducible) (he : a.concat b = c.concat d) :
    a.height = c.height := by
  apply le_antisymm
  · by_contra hn
    have hh : c.height < a.height := by omega
    have hf : (a.concat b).crossingCount c.height = 1 := by rw [he]; exact concat_crossing_at _ _
    rw [concat_crossing_below _ _ _ hh] at hf
    exact ha _ c.height_pos hh hf
  · by_contra hn
    have hh : a.height < c.height := by omega
    have hf : (c.concat d).crossingCount a.height = 1 := by rw [← he]; exact concat_crossing_at _ _
    rw [concat_crossing_below _ _ _ hh] at hf
    exact hc _ a.height_pos hh hf

end HoneycombActual.Bridge

end

end OAI
