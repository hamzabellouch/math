import Mathlib

namespace OAI

namespace Problem310.TreePreorderRank

/-- Number of nodes, including the root, in the complete `K`-ary tree of depth `d`. -/
def size (K : ℕ) : ℕ → ℕ
  | 0 => 1
  | d + 1 => 1 + K * size K d

/-- Preorder rank of a path. On paths of length at most `d`, this is the usual
zero-based root-first rank in the complete tree. -/
def rank {K : ℕ} : ℕ → List (Fin K) → ℕ
  | 0, _ => 0
  | _ + 1, [] => 0
  | d + 1, i :: p => 1 + i.val * size K d + rank d p

@[simp] theorem size_zero (K : ℕ) : size K 0 = 1 := rfl
@[simp] theorem size_succ (K d : ℕ) : size K (d + 1) = 1 + K * size K d := rfl
@[simp] theorem rank_nil {K : ℕ} (d : ℕ) : rank d ([] : List (Fin K)) = 0 := by
  cases d <;> rfl
@[simp] theorem rank_cons {K : ℕ} (d : ℕ) (i : Fin K) (p : List (Fin K)) :
    rank (d + 1) (i :: p) = 1 + i.val * size K d + rank d p := rfl

theorem size_pos (K d : ℕ) : 0 < size K d := by
  cases d <;> simp [size]

/-- Every valid node has rank strictly below the total number of nodes. -/
theorem rank_lt_size {K d : ℕ} {p : List (Fin K)} (hp : p.length ≤ d) :
    rank d p < size K d := by
  induction d generalizing p with
  | zero => simp [rank, size]
  | succ d ih =>
    cases p with
    | nil => simp [rank, size]
    | cons i p =>
      have hp' : p.length ≤ d := by simpa using hp
      have hr := ih hp'
      have hi : i.val + 1 ≤ K := i.isLt
      have hm := Nat.mul_le_mul_right (size K d) hi
      simp only [rank_cons, size_succ]
      nlinarith

/-- A nonroot valid node has positive rank. -/
theorem rank_pos {K d : ℕ} {p : List (Fin K)}
    (hp : p.length ≤ d) (hne : p ≠ []) : 0 < rank d p := by
  cases p with
  | nil => exact (hne rfl).elim
  | cons i p =>
    cases d with
    | zero => simp at hp
    | succ d => simp [rank]

/-- Descending into a node adds the local preorder rank in that node's subtree. -/
theorem rank_append {K d : ℕ} {p : List (Fin K)} (hp : p.length ≤ d)
    (q : List (Fin K)) :
    rank d (p ++ q) = rank d p + rank (d - p.length) q := by
  induction p generalizing d with
  | nil => simp
  | cons i p ih =>
    cases d with
    | zero => simp at hp
    | succ d =>
      have hp' : p.length ≤ d := by simpa using hp
      simp only [List.cons_append, rank_cons, List.length_cons, Nat.add_sub_add_right]
      rw [ih hp']
      omega

/-- A subtree occupies one contiguous interval of the preorder ranks. -/
theorem rank_append_bounds {K d : ℕ} {p q : List (Fin K)}
    (hpq : (p ++ q).length ≤ d) :
    rank d p ≤ rank d (p ++ q) ∧
      rank d (p ++ q) < rank d p + size K (d - p.length) := by
  have hp : p.length ≤ d := by simp only [List.length_append] at hpq; omega
  have hq : q.length ≤ d - p.length := by simp only [List.length_append] at hpq; omega
  rw [rank_append hp]
  exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left (rank_lt_size hq) _⟩

/-- Every strict descendant occurs after its ancestor in preorder. -/
theorem rank_lt_rank_append {K d : ℕ} {p q : List (Fin K)}
    (hpq : (p ++ q).length ≤ d) (hq : q ≠ []) : rank d p < rank d (p ++ q) := by
  have hp : p.length ≤ d := by simp only [List.length_append] at hpq; omega
  have hqd : q.length ≤ d - p.length := by simp only [List.length_append] at hpq; omega
  rw [rank_append hp]
  exact Nat.lt_add_of_pos_right (rank_pos hqd hq)

/-- The entire subtree of an earlier child precedes the entire subtree of a later child. -/
theorem rank_cons_lt_rank_cons {K d : ℕ} {i j : Fin K} {p q : List (Fin K)}
    (hij : i < j) (hp : p.length ≤ d) (_hq : q.length ≤ d) :
    rank (d + 1) (i :: p) < rank (d + 1) (j :: q) := by
  have hr := rank_lt_size hp
  have hi : i.val + 1 ≤ j.val := hij
  have hm := Nat.mul_le_mul_right (size K d) hi
  simp only [rank_cons]
  nlinarith

/-- Ordered sibling subtrees remain ordered after any common ancestral prefix. -/
theorem rank_sibling_descendants_lt {K d : ℕ} {P p q : List (Fin K)} {i j : Fin K}
    (hij : i < j) (hp : (P ++ i :: p).length ≤ d)
    (hq : (P ++ j :: q).length ≤ d) :
    rank d (P ++ i :: p) < rank d (P ++ j :: q) := by
  have hP : P.length ≤ d := by simp only [List.length_append, List.length_cons] at hp; omega
  rw [rank_append hP, rank_append hP]
  cases heq : d - P.length with
  | zero => simp only [List.length_append, List.length_cons] at hp; omega
  | succ k =>
    have hp' : p.length ≤ k := by simp only [List.length_append, List.length_cons] at hp; omega
    have hq' : q.length ≤ k := by simp only [List.length_append, List.length_cons] at hq; omega
    exact Nat.add_lt_add_left (rank_cons_lt_rank_cons hij hp' hq') _

/-- Preorder ranks distinguish every two valid paths. -/
theorem rank_injective_on {K d : ℕ} {p q : List (Fin K)}
    (hp : p.length ≤ d) (hq : q.length ≤ d) (heq : rank d p = rank d q) : p = q := by
  induction d generalizing p q with
  | zero =>
    have hp0 : p = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hp)
    have hq0 : q = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hq)
    exact hp0.trans hq0.symm
  | succ d ih =>
    cases p with
    | nil =>
      cases q with
      | nil => rfl
      | cons j q => simp only [rank_nil, rank_cons] at heq; omega
    | cons i p =>
      cases q with
      | nil => simp [rank] at heq
      | cons j q =>
        have hp' : p.length ≤ d := by simpa using hp
        have hq' : q.length ≤ d := by simpa using hq
        have hij : i = j := by
          rcases lt_trichotomy i j with h | h | h
          · exact False.elim ((rank_cons_lt_rank_cons h hp' hq').ne heq)
          · exact h
          · exact False.elim ((rank_cons_lt_rank_cons h hq' hp').ne heq.symm)
        subst j
        have heq' : rank d p = rank d q := by simpa only [rank_cons, Nat.add_left_cancel_iff] using heq
        exact congrArg (List.cons i) (ih hp' hq' heq')

/-- The interval occupied by a subtree is contained in the whole tree's interval. -/
theorem subtree_end_le_size {K d : ℕ} {p : List (Fin K)} (hp : p.length ≤ d) :
    rank d p + size K (d - p.length) ≤ size K d := by
  induction d generalizing p with
  | zero => simp [rank, size]
  | succ d ih =>
    cases p with
    | nil => simp
    | cons i p =>
      have hp' : p.length ≤ d := by simpa using hp
      have he := ih hp'
      have hi : i.val + 1 ≤ K := i.isLt
      have hm := Nat.mul_le_mul_right (size K d) hi
      simp only [rank_cons, List.length_cons, Nat.add_sub_add_right, size_succ]
      nlinarith

/-- The descendants of a path are exactly a contiguous half-open interval of ranks. -/
theorem isPrefix_iff_rank_bounds {K d : ℕ} {p q : List (Fin K)}
    (hp : p.length ≤ d) (hq : q.length ≤ d) :
    List.IsPrefix p q ↔ rank d p ≤ rank d q ∧
      rank d q < rank d p + size K (d - p.length) := by
  constructor
  · rintro ⟨s, rfl⟩
    exact rank_append_bounds hq
  · intro h
    induction d generalizing p q with
    | zero =>
      have hp0 : p = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hp)
      subst p
      exact List.nil_prefix
    | succ d ih =>
      cases p with
      | nil => exact List.nil_prefix
      | cons i p =>
        cases q with
        | nil =>
          have hpos := rank_pos hp (by simp)
          simp only [rank_nil] at h
          omega
        | cons j q =>
          have hp' : p.length ≤ d := by simpa using hp
          have hq' : q.length ≤ d := by simpa using hq
          have hpEnd := subtree_end_le_size hp'
          have hrq := rank_lt_size hq'
          simp only [rank_cons, List.length_cons, Nat.add_sub_add_right] at h
          have hij : i = j := by
            rcases lt_trichotomy i j with hij | hij | hji
            · have hi : i.val + 1 ≤ j.val := hij
              have hm := Nat.mul_le_mul_right (size K d) hi
              exfalso
              nlinarith [h.2]
            · exact hij
            · have hi : j.val + 1 ≤ i.val := hji
              have hm := Nat.mul_le_mul_right (size K d) hi
              exfalso
              nlinarith [h.1]
          subst j
          apply List.cons_prefix_cons.mpr
          refine ⟨rfl, ih hp' hq' ?_⟩
          omega

/-- Zero-based rank among edges, obtained by removing the root's rank. -/
def edgeRank {K : ℕ} (d : ℕ) (p : List (Fin K)) : ℕ := rank d p - 1

theorem edgeRank_add_one {K d : ℕ} {p : List (Fin K)}
    (hp : p.length ≤ d) (hne : p ≠ []) : edgeRank d p + 1 = rank d p := by
  have := rank_pos hp hne
  unfold edgeRank
  omega

theorem edgeRank_lt {K d : ℕ} {p : List (Fin K)}
    (hp : p.length ≤ d) (hne : p ≠ []) : edgeRank d p < size K d - 1 := by
  have := rank_lt_size hp
  have := rank_pos hp hne
  unfold edgeRank
  omega

theorem edgeRank_injective_on {K d : ℕ} {p q : List (Fin K)}
    (hp : p.length ≤ d) (hq : q.length ≤ d) (hp0 : p ≠ []) (hq0 : q ≠ [])
    (heq : edgeRank d p = edgeRank d q) : p = q := by
  apply rank_injective_on hp hq
  rw [← edgeRank_add_one hp hp0, ← edgeRank_add_one hq hq0, heq]

theorem edgeRank_lt_edgeRank_append {K d : ℕ} {p q : List (Fin K)}
    (hpq : (p ++ q).length ≤ d) (hp0 : p ≠ []) (hq0 : q ≠ []) :
    edgeRank d p < edgeRank d (p ++ q) := by
  have hlt := rank_lt_rank_append hpq hq0
  have hp : p.length ≤ d := by simp only [List.length_append] at hpq; omega
  have hpos := rank_pos hp hp0
  unfold edgeRank
  omega

theorem edgeRank_sibling_descendants_lt {K d : ℕ} {P p q : List (Fin K)} {i j : Fin K}
    (hij : i < j) (hp : (P ++ i :: p).length ≤ d)
    (hq : (P ++ j :: q).length ≤ d) :
    edgeRank d (P ++ i :: p) < edgeRank d (P ++ j :: q) := by
  have hlt := rank_sibling_descendants_lt hij hp hq
  have hpos := rank_pos hp (by simp)
  unfold edgeRank
  omega

/-- Edge ranks give the same exact contiguous-subtree characterization without the root slot. -/
theorem isPrefix_iff_edgeRank_bounds {K d : ℕ} {p q : List (Fin K)}
    (hp : p.length ≤ d) (hq : q.length ≤ d) (hp0 : p ≠ []) (hq0 : q ≠ []) :
    List.IsPrefix p q ↔ edgeRank d p ≤ edgeRank d q ∧
      edgeRank d q < edgeRank d p + size K (d - p.length) := by
  rw [isPrefix_iff_rank_bounds hp hq]
  have hpR := edgeRank_add_one hp hp0
  have hqR := edgeRank_add_one hq hq0
  omega

end Problem310.TreePreorderRank

end OAI
