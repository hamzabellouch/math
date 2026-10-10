import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace OAI

/-!
# Cached tournament for merging row fronts

Each leaf holds at most one current occurrence of a row. Internal nodes
cache the smaller child winner. Reading the winner is constant time;
replacing one leaf recomputes just its root path. The candidate list below
is an analysis view and is never stored in the tournament.
-/

namespace LowSpaceSubsetSum
namespace Tournament

universe u

variable {α : Type u}

def pick (key : α → ℤ) : Option α → Option α → Option α
  | none, v => v
  | u, none => u
  | some x, some y => if key x ≤ key y then some x else some y

theorem pick_member (key : α → ℤ) (u v : Option α) {x : α}
    (h : pick key u v = some x) : u = some x ∨ v = some x := by
  cases u with
  | none => exact Or.inr h
  | some a =>
    cases v with
    | none => exact Or.inl h
    | some b =>
      by_cases hab : key a ≤ key b
      · exact Or.inl (by simpa [pick, hab] using h)
      · exact Or.inr (by simpa [pick, hab] using h)

theorem pick_le_left (key : α → ℤ) (a : α) (v : Option α) :
    ∃ x, pick key (some a) v = some x ∧ key x ≤ key a := by
  cases v with
  | none => exact ⟨a, rfl, le_rfl⟩
  | some b =>
    by_cases hab : key a ≤ key b
    · exact ⟨a, by simp [pick, hab], le_rfl⟩
    · exact ⟨b, by simp [pick, hab], (not_le.mp hab).le⟩

theorem pick_le_right (key : α → ℤ) (u : Option α) (b : α) :
    ∃ x, pick key u (some b) = some x ∧ key x ≤ key b := by
  cases u with
  | none => exact ⟨b, rfl, le_rfl⟩
  | some a =>
    by_cases hab : key a ≤ key b
    · exact ⟨a, by simp [pick, hab], hab⟩
    · exact ⟨b, by simp [pick, hab], le_rfl⟩

def Best (key : α → ℤ) (v : Option α) (xs : List α) : Prop :=
  (∀ x, v = some x → x ∈ xs) ∧ (∀ y ∈ xs, ∃ x, v = some x ∧ key x ≤ key y)

theorem best_append (key : α → ℤ) {u v : Option α} {xs ys : List α}
    (hu : Best key u xs) (hv : Best key v ys) :
    Best key (pick key u v) (xs ++ ys) := by
  constructor
  · intro x hx
    rcases pick_member key u v hx with hx | hx
    · exact List.mem_append_left _ (hu.1 x hx)
    · exact List.mem_append_right _ (hv.1 x hx)
  · intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · obtain ⟨z, hz, hzy⟩ := hu.2 y hy
      obtain ⟨x, hx, hxz⟩ := pick_le_left key z v
      rw [← hz] at hx
      exact ⟨x, hx, hxz.trans hzy⟩
    · obtain ⟨z, hz, hzy⟩ := hv.2 y hy
      obtain ⟨x, hx, hxz⟩ := pick_le_right key u z
      rw [← hz] at hx
      exact ⟨x, hx, hxz.trans hzy⟩

inductive Tree (α : Type u) : ℕ → Type u
  | leaf (value : Option α) : Tree α 0
  | node {d : ℕ} (winner : Option α) (left right : Tree α d) : Tree α (d + 1)

def winner {d : ℕ} : Tree α d → Option α
  | .leaf v => v
  | .node v _ _ => v

def candidates {d : ℕ} : Tree α d → List α
  | .leaf v => v.toList
  | .node _ l r => candidates l ++ candidates r

def Valid (key : α → ℤ) {d : ℕ} : Tree α d → Prop
  | .leaf _ => True
  | .node v l r => v = pick key (winner l) (winner r) ∧ Valid key l ∧ Valid key r

def node (key : α → ℤ) {d : ℕ} (l r : Tree α d) : Tree α (d + 1) :=
  .node (pick key (winner l) (winner r)) l r

theorem winner_best (key : α → ℤ) {d : ℕ} (t : Tree α d) (ht : Valid key t) :
    Best key (winner t) (candidates t) := by
  induction t with
  | leaf v => cases v <;> simp [winner, candidates, Best]
  | node v l r ihl ihr =>
    obtain ⟨hv, hl, hr⟩ := ht
    change Best key v (candidates l ++ candidates r)
    rw [hv]
    exact best_append key (ihl hl) (ihr hr)

theorem winner_none_iff (key : α → ℤ) {d : ℕ} (t : Tree α d) (ht : Valid key t) :
    winner t = none ↔ candidates t = [] := by
  have hb := winner_best key t ht
  constructor
  · intro hn
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro y hy
    obtain ⟨x, hx, _⟩ := hb.2 y hy
    simp [hn] at hx
  · intro hn
    cases hw : winner t with
    | none => rfl
    | some x => simpa [hn] using hb.1 x hw

def lookup : {d : ℕ} → Tree α d → (Fin d → Bool) → Option α
  | 0, .leaf v, _ => v
  | _d + 1, .node _ l r, path =>
    if path 0 then lookup r (fun i => path i.succ) else lookup l (fun i => path i.succ)

def replace (key : α → ℤ) : {d : ℕ} → Tree α d → (Fin d → Bool) → Option α → Tree α d
  | 0, .leaf _, _, v => .leaf v
  | _d + 1, .node _ l r, path, v =>
    if path 0 then node key l (replace key r (fun i => path i.succ) v)
    else node key (replace key l (fun i => path i.succ) v) r

theorem replace_valid (key : α → ℤ) {d : ℕ} (t : Tree α d)
    (ht : Valid key t) (path : Fin d → Bool) (v : Option α) :
    Valid key (replace key t path v) := by
  induction t with
  | leaf _ => trivial
  | node w l r ihl ihr =>
    obtain ⟨_, hl, hr⟩ := ht
    simp only [replace]
    split
    · exact ⟨rfl, hl, ihr hr _⟩
    · exact ⟨rfl, ihl hl _, hr⟩

theorem lookup_replace_same (key : α → ℤ) {d : ℕ} (t : Tree α d)
    (path : Fin d → Bool) (v : Option α) : lookup (replace key t path v) path = v := by
  induction t with
  | leaf _ => rfl
  | node w l r ihl ihr =>
    simp only [replace]
    split <;> simp_all [node, lookup]

theorem lookup_replace (key : α → ℤ) {d : ℕ} (t : Tree α d)
    (path q : Fin d → Bool) (v : Option α) :
    lookup (replace key t path v) q = if path = q then v else lookup t q := by
  induction t with
  | leaf _ =>
    have heq : path = q := Subsingleton.elim _ _
    simp [replace, lookup, heq]
  | @node d w l r ihl ihr =>
    have heq : path = q ↔ path 0 = q 0 ∧
        (fun i : Fin d => path i.succ) = (fun i : Fin d => q i.succ) := by
      constructor
      · intro h
        subst q
        exact ⟨rfl, rfl⟩
      · rintro ⟨hh, ht⟩
        funext i
        exact Fin.cases hh (fun j => congrFun ht j) i
    cases hp : path 0 <;> cases hq : q 0 <;>
      simp [replace, node, lookup, hp, hq, ihl, ihr, heq]

def build (key : α → ℤ) : (d : ℕ) → ((Fin d → Bool) → Option α) → Tree α d
  | 0, front => .leaf (front Fin.elim0)
  | d + 1, front => node key
    (build key d (fun p => front (Fin.cons false p)))
    (build key d (fun p => front (Fin.cons true p)))

theorem build_valid (key : α → ℤ) (d : ℕ) (front : (Fin d → Bool) → Option α) :
    Valid key (build key d front) := by
  induction d with
  | zero => trivial
  | succ d ih => exact ⟨rfl, ih _, ih _⟩

theorem lookup_build (key : α → ℤ) (d : ℕ) (front : (Fin d → Bool) → Option α)
    (path : Fin d → Bool) : lookup (build key d front) path = front path := by
  induction d with
  | zero =>
    have hpath : (Fin.elim0 : Fin 0 → Bool) = path := Subsingleton.elim _ _
    simpa [build, lookup] using congrArg front hpath
  | succ d ih =>
    simp only [build, node, lookup]
    cases hp : path 0
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ih]
      apply congrArg front
      funext i
      exact Fin.cases (by simp [hp]) (fun j => by simp) i
    · simp only [↓reduceIte]
      rw [ih]
      apply congrArg front
      funext i
      exact Fin.cases (by simp [hp]) (fun j => by simp) i

theorem mem_candidates_iff {d : ℕ} (t : Tree α d) (v : α) :
    v ∈ candidates t ↔ ∃ path, lookup t path = some v := by
  induction t with
  | leaf w =>
    constructor
    · intro hv
      exact ⟨Fin.elim0, by simpa [candidates, lookup] using hv⟩
    · rintro ⟨_, hv⟩
      simpa [candidates, lookup] using hv
  | @node d w l r ihl ihr =>
    rw [candidates, List.mem_append, ihl, ihr]
    constructor
    · rintro (⟨p, hp⟩ | ⟨p, hp⟩)
      · exact ⟨Fin.cons false p, by simpa [lookup] using hp⟩
      · exact ⟨Fin.cons true p, by simpa [lookup] using hp⟩
    · rintro ⟨p, hp⟩
      cases h : p 0
      · exact Or.inl ⟨fun i => p i.succ, by simpa [lookup, h] using hp⟩
      · exact Or.inr ⟨fun i => p i.succ, by simpa [lookup, h] using hp⟩

theorem winner_le_lookup (key : α → ℤ) {d : ℕ} (t : Tree α d) (ht : Valid key t)
    (path : Fin d → Bool) {v : α} (hv : lookup t path = some v) :
    ∃ w, winner t = some w ∧ key w ≤ key v :=
  (winner_best key t ht).2 v ((mem_candidates_iff t v).mpr ⟨path, hv⟩)

def nodes : {d : ℕ} → Tree α d → ℕ
  | 0, .leaf _ => 1
  | _ + 1, .node _ l r => 1 + nodes l + nodes r

theorem nodes_exact {d : ℕ} (t : Tree α d) : nodes t + 1 = 2 ^ (d + 1) := by
  induction t with
  | leaf _ => norm_num [nodes]
  | @node d w l r ihl ihr =>
    simp only [nodes]
    rw [pow_succ]
    omega

theorem padded_nodes_le (R : ℕ) (t : Tree α (Nat.clog 2 R)) :
    nodes t + 1 ≤ 4 * (R + 1) := by
  rw [nodes_exact, pow_succ]
  by_cases hR : R ≤ 1
  · rw [Nat.clog_of_right_le_one hR]
    norm_num
    omega
  · have hR' : 1 < R := by omega
    have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hR'
    have hpos := Nat.clog_pos (by decide : 1 < 2) hR'
    have hbits : 2 ^ Nat.clog 2 R ≤ 2 * R := by
      rw [show Nat.clog 2 R = (Nat.clog 2 R).pred + 1 from
        (Nat.succ_pred_eq_of_pos hpos).symm, pow_succ]
      omega
    omega

theorem depth_le_index_bits {R n : ℕ} (hR : R ≤ 2 ^ n) : Nat.clog 2 R ≤ n :=
  Nat.clog_le_of_le_pow hR

/-- Number of cached comparisons made by a leaf replacement. -/
def replaceComparisons : {d : ℕ} → Tree α d → (Fin d → Bool) → ℕ
  | 0, .leaf _, _ => 0
  | _d + 1, .node _ l r, path =>
    1 + if path 0 then replaceComparisons r (fun i => path i.succ)
      else replaceComparisons l (fun i => path i.succ)

theorem replaceComparisons_eq {d : ℕ} (t : Tree α d) (path : Fin d → Bool) :
    replaceComparisons t path = d := by
  induction t with
  | leaf _ => rfl
  | @node d w l r ihl ihr =>
    simp only [replaceComparisons]
    split <;> simp [ihl, ihr, Nat.add_comm]

end Tournament
end LowSpaceSubsetSum

end OAI
