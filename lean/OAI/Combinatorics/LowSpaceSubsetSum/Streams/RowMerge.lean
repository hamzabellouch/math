import OAI.Combinatorics.LowSpaceSubsetSum.Streams.Tournament
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.CyclicCursor

namespace OAI

/-!
# A tournament merge with one current occurrence per row

The shared immutable input arrays are parameters of the row reader. Each
leaf contains a row identifier, its current item, and its cursor after that
item. Advancing the winning row performs one row read and one tournament
replacement. The remaining lists below are ghost views used for correctness;
the merge state stores no pair-product list.
-/

namespace LowSpaceSubsetSum
namespace RowMerge

universe u v

variable {α : Type u} {σ : Type v} {d : ℕ}

abbrev Path (d : ℕ) := Fin d → Bool

structure Front (d : ℕ) (α : Type u) (σ : Type v) where
  row : Path d
  value : α
  after : σ

def front (read : σ → Option (α × σ)) (p : Path d) (s : σ) : Option (Front d α σ) :=
  (read s).map (fun z => ⟨p, z.1, z.2⟩)

def start (key : α → ℤ) (read : σ → Option (α × σ)) (s : Path d → σ) :
    Tournament.Tree (Front d α σ) d :=
  Tournament.build (fun x => key x.value) d (fun p => front read p (s p))

def Aligned (t : Tournament.Tree (Front d α σ) d) : Prop :=
  ∀ p x, Tournament.lookup t p = some x → x.row = p

theorem front_row (read : σ → Option (α × σ)) (p : Path d) (s : σ)
    {x : Front d α σ} (hx : front read p s = some x) : x.row = p := by
  cases hr : read s with
  | none => simp [front, hr] at hx
  | some z =>
    have heq : (⟨p, z.1, z.2⟩ : Front d α σ) = x := by simpa [front, hr] using hx
    rw [← heq]

theorem start_aligned (key : α → ℤ) (read : σ → Option (α × σ)) (s : Path d → σ) :
    Aligned (start key read s) := by
  intro p x hx
  rw [start, Tournament.lookup_build] at hx
  exact front_row read p (s p) hx

theorem start_valid (key : α → ℤ) (read : σ → Option (α × σ)) (s : Path d → σ) :
    Tournament.Valid (fun x => key x.value) (start key read s) :=
  Tournament.build_valid _ _ _

def advance (key : α → ℤ) (read : σ → Option (α × σ))
    (t : Tournament.Tree (Front d α σ) d) :
    Option (α × Tournament.Tree (Front d α σ) d) :=
  (Tournament.winner t).map fun x =>
    (x.value, Tournament.replace (fun y => key y.value) t x.row (front read x.row x.after))

theorem advance_valid (key : α → ℤ) (read : σ → Option (α × σ))
    (t : Tournament.Tree (Front d α σ) d)
    (ht : Tournament.Valid (fun x => key x.value) t) {a : α}
    {t' : Tournament.Tree (Front d α σ) d} (ha : advance key read t = some (a, t')) :
    Tournament.Valid (fun x => key x.value) t' := by
  cases hw : Tournament.winner t with
  | none => simp [advance, hw] at ha
  | some x =>
    have heq : (x.value, Tournament.replace (fun y => key y.value) t x.row
        (front read x.row x.after)) = (a, t') := by simpa [advance, hw] using ha
    rw [← (Prod.mk.inj heq).2]
    exact Tournament.replace_valid _ t ht _ _

theorem advance_aligned (key : α → ℤ) (read : σ → Option (α × σ))
    (t : Tournament.Tree (Front d α σ) d) (ht : Aligned t) {a : α}
    {t' : Tournament.Tree (Front d α σ) d} (ha : advance key read t = some (a, t')) :
    Aligned t' := by
  cases hw : Tournament.winner t with
  | none => simp [advance, hw] at ha
  | some x =>
    have heq : (x.value, Tournament.replace (fun y => key y.value) t x.row
        (front read x.row x.after)) = (a, t') := by simpa [advance, hw] using ha
    rw [← (Prod.mk.inj heq).2]
    intro p y hy
    rw [Tournament.lookup_replace] at hy
    by_cases hp : x.row = p
    · rw [ite_eq_left hp] at hy
      exact (front_row read x.row x.after hy).trans hp
    · rw [ite_eq_right hp] at hy
      exact ht p y hy

theorem winner_at_own_row (key : α → ℤ) (t : Tournament.Tree (Front d α σ) d)
    (ht : Tournament.Valid (fun x => key x.value) t) (halign : Aligned t)
    {x : Front d α σ} (hx : Tournament.winner t = some x) :
    Tournament.lookup t x.row = some x := by
  have hm := (Tournament.winner_best (fun x => key x.value) t ht).1 x hx
  obtain ⟨p, hp⟩ := (Tournament.mem_candidates_iff t x).mp hm
  rw [halign p x hp]
  exact hp

theorem winner_is_minimum (key : α → ℤ) (t : Tournament.Tree (Front d α σ) d)
    (ht : Tournament.Valid (fun x => key x.value) t) {x : Front d α σ}
    (hx : Tournament.winner t = some x) (p : Path d) {y : Front d α σ}
    (hy : Tournament.lookup t p = some y) : key x.value ≤ key y.value := by
  obtain ⟨w, hw, hwy⟩ := Tournament.winner_le_lookup (fun x => key x.value) t ht p hy
  have h : w = x := Option.some.inj (hw.symm.trans hx)
  simpa [h] using hwy

/-- A row reader's finite output law, used only in the correctness proof. -/
def IsReader (read : σ → Option (α × σ)) (view : σ → List α) : Prop :=
  ∀ s, match read s with
    | none => view s = []
    | some (a, s') => view s = a :: view s'

theorem cyclic_next_reader (xs : Array α) [NeZero xs.size] :
    IsReader (CyclicCursor.next xs)
      (fun c => CyclicCursor.trace (fun i : Fin xs.size => xs[i.val]) c.remaining c) := by
  intro c
  cases h : c.remaining with
  | zero => simp [CyclicCursor.next, CyclicCursor.trace, h]
  | succ k =>
    simp [CyclicCursor.next, CyclicCursor.trace, h, CyclicCursor.advance_remaining]

def remaining (view : σ → List α) (t : Tournament.Tree (Front d α σ) d)
    (p : Path d) : List α :=
  match Tournament.lookup t p with
  | none => []
  | some x => x.value :: view x.after

theorem start_remaining (key : α → ℤ) (read : σ → Option (α × σ))
    (view : σ → List α) (hread : IsReader read view) (s : Path d → σ) (p : Path d) :
    remaining view (start key read s) p = view (s p) := by
  simp only [remaining, start, Tournament.lookup_build, front]
  have hr := hread (s p)
  cases h : read (s p) with
  | none =>
    simp only [h] at hr
    simpa using hr.symm
  | some z =>
    simp only [h] at hr
    simpa using hr.symm

theorem replace_remaining (key : α → ℤ) (read : σ → Option (α × σ))
    (view : σ → List α) (hread : IsReader read view)
    (t : Tournament.Tree (Front d α σ) d) (x : Front d α σ) (q : Path d) :
    remaining view (Tournament.replace (fun y => key y.value) t x.row
        (front read x.row x.after)) q =
      if x.row = q then view x.after else remaining view t q := by
  unfold remaining
  rw [Tournament.lookup_replace]
  by_cases hq : x.row = q
  · rw [ite_eq_left hq, ite_eq_left hq]
    have hr := hread x.after
    cases h : read x.after with
    | none =>
      simp only [h] at hr
      simpa [front, h] using hr.symm
    | some z =>
      simp only [h] at hr
      simpa [front, h] using hr.symm
  · rw [ite_eq_right hq, ite_eq_right hq]

def potential (view : σ → List α) (t : Tournament.Tree (Front d α σ) d) : ℕ :=
  ∑ p : Path d, (remaining view t p).length

theorem replacement_consumes_one (key : α → ℤ) (read : σ → Option (α × σ))
    (view : σ → List α) (hread : IsReader read view)
    (t : Tournament.Tree (Front d α σ) d)
    (ht : Tournament.Valid (fun y => key y.value) t) (halign : Aligned t)
    {x : Front d α σ} (hx : Tournament.winner t = some x) :
    potential view (Tournament.replace (fun y => key y.value) t x.row
      (front read x.row x.after)) + 1 = potential view t := by
  have hrow := winner_at_own_row key t ht halign hx
  let t' := Tournament.replace (fun y => key y.value) t x.row (front read x.row x.after)
  have hpoint (p : Path d) : (remaining view t p).length =
      (remaining view t' p).length + if p = x.row then 1 else 0 := by
    have hnew := replace_remaining key read view hread t x p
    change remaining view t' p = _ at hnew
    by_cases hp : p = x.row
    · subst p
      rw [ite_eq_left rfl] at hnew
      rw [hnew]
      simp [remaining, hrow]
    · rw [ite_eq_right (Ne.symm hp)] at hnew
      rw [hnew, ite_eq_right hp]
      omega
  unfold potential
  rw [show (∑ p : Path d, (remaining view t p).length) =
      ∑ p : Path d, ((remaining view t' p).length + if p = x.row then 1 else 0) from
    Finset.sum_congr rfl (fun p _ => hpoint p)]
  simp [Finset.sum_add_distrib, t']

end RowMerge
end LowSpaceSubsetSum

end OAI
