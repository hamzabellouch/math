import OAI.Combinatorics.LowSpaceSubsetSum.Counting.SamplerExecution

namespace OAI

/-! # Materializing the finite permutation sampler's choices

The sampler's recursive finite-range choices are stored as integer digits.
The construction below executes the same `decomposeFin` permutation using
arrays, so applying the resulting permutation is a bounded array lookup.
-/

namespace LowSpaceSubsetSum.PermutationArray

abbrev Digits : ℕ → Type
  | 0 => Unit
  | k + 1 => Fin (k + 1) × Digits k

def semantic : (k : ℕ) → Digits k → Equiv.Perm (Fin k)
  | 0, _ => Equiv.refl _
  | k + 1, (p, rest) => Equiv.Perm.decomposeFin.symm (p, semantic k rest)

def grow {k : ℕ} (p : Fin (k + 1)) (v : Vector (Fin k) k) :
    Vector (Fin (k + 1)) (k + 1) :=
  Vector.ofFn (Fin.cases p (fun i => Equiv.swap 0 p (v[i.val]).succ))

def build : (k : ℕ) → Digits k → Vector (Fin k) k × ℕ
  | 0, _ => (Vector.ofFn Fin.elim0, 1)
  | k + 1, (p, rest) =>
    let previous := build k rest
    (grow p previous.1, previous.2 + 10 * (k + 1) + 3)

theorem grow_value {k : ℕ} (p : Fin (k + 1)) (v : Vector (Fin k) k)
    (e : Equiv.Perm (Fin k)) (hv : ∀ i : Fin k, v[i.val] = e i) (i : Fin (k + 1)) :
    (grow p v)[i.val] = Equiv.Perm.decomposeFin.symm (p, e) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [grow, Vector.getElem_ofFn, Fin.eta, Fin.cases_zero,
      Equiv.Perm.decomposeFin_symm_apply_zero]
  · simp only [grow, Vector.getElem_ofFn, Fin.eta, Fin.cases_succ, hv,
      Equiv.Perm.decomposeFin_symm_apply_succ]

theorem build_value (k : ℕ) (digits : Digits k) (i : Fin k) :
    (build k digits).1[i.val] = semantic k digits i := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    rcases digits with ⟨p, rest⟩
    exact grow_value p (build k rest).1 (semantic k rest) (ih rest) i

theorem build_work (k : ℕ) (digits : Digits k) :
    (build k digits).2 ≤ 10 * (k + 1) ^ 2 := by
  induction k with
  | zero => simp [build]
  | succ k ih =>
    rcases digits with ⟨p, rest⟩
    have hp := ih rest
    change (build k rest).2 + 10 * (k + 1) + 3 ≤ _
    nlinarith only [hp]

def lookup {k : ℕ} (v : Vector (Fin k) k) (i : Fin k) : Fin k × ℕ := (v[i.val], 1)

theorem lookup_value (k : ℕ) (digits : Digits k) (i : Fin k) :
    (lookup (build k digits).1 i).1 = semantic k digits i := build_value k digits i

/-- The old and new arrays may coexist during one extension, together with
the recursive digit stack. All are linear in the ambient input length. -/
def peakCells : ℕ → ℕ
  | 0 => 3
  | k + 1 => max (peakCells k + 2) (3 * (k + 1) + 5)

theorem peakCells_bound (k : ℕ) : peakCells k ≤ 5 * (k + 1) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [peakCells]
    apply max_le <;> omega

end LowSpaceSubsetSum.PermutationArray

end OAI
