import OAI.Combinatorics.BinaryEdit.FiniteVectors
import OAI.Combinatorics.BinaryEdit.SparseCharacterPeriod
import OAI.Combinatorics.BinaryEdit.FiniteActivityBridge

namespace OAI

/-!
# Actual sparse-node character tests

Short-period detection holds for the finite-tree vectors in both the
function-indexed and list-indexed presentations.
-/

noncomputable section

open scoped BigOperators
open Classical

namespace TreeEdit.BinaryLower.FiniteVectors

/-- The actual finite-tree cheap vector detects any active distinguished
vector whose children have support smaller than `k`. Exact orders and
primality are unnecessary here: the proved annihilating periods suffice. -/
theorem sparse_node_detection {m k : ℕ}
    (p : Fin k → Fin m → ℕ) (hk : 1 ≤ k)
    (hppos : ∀ q i, 0 < p q i) (hp : ∀ q i, p q i ≤ k ^ 5)
    (j : ℕ) (hj : j < k) (a : Leaf m k) (χ : AddChar (State p) ℂ)
    (hactive : χ (w p j a) ≠ 1)
    (hsparse : (Finset.univ.filter fun i : Fin m =>
      χ (w p (j + 1) (Function.update a ⟨j, hj⟩ i)) ≠ 1).card < k) :
    ((4 * k ^ (10 * k) : ℕ) : ℝ) ≤
      ∑ s : Fin (4 * k ^ (10 * k)), ‖1 - χ ((s.val + 1) • u p j a)‖ ^ 2 := by
  let : Finite (State p) := state_finite p hppos
  let child : Fin m → State p := fun i => w p (j + 1) (Function.update a ⟨j, hj⟩ i)
  let S : Finset (Fin m) := Finset.univ.filter fun i => χ (child i) ≠ 1
  have hsum : u p j a = ∑ i, child i := u_eq_sum_child_w p j hj a
  have hroot : χ (levelProduct p ⟨j, hj⟩ • ∑ i, child i) ≠ 1 := by
    rw [← hsum, ← w_eq_level_nsmul_u p j hj a]
    exact hactive
  have hchild : ∀ i ∈ S, (prefixPeriod p j a * p ⟨j, hj⟩ i) • child i = 0 := by
    intro i _
    dsimp [child]
    rw [← prefixPeriod_child p j hj a i]
    exact prefixPeriod_nsmul_w p (j + 1) (Function.update a ⟨j, hj⟩ i)
  have houtside : ∀ i, i ∉ S → χ (child i) = 1 := by
    intro i hi
    simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hi
  have havg := FinitePeriod.sparse_character_detection χ S child (p ⟨j, hj⟩)
    hk hj hsparse (prefixPeriod_pos p hppos j a) (prefixPeriod_le p hp j hj.le a)
    (fun i _ => hppos _ i) (fun i _ => hp _ i) houtside hchild hroot
  have hJ : (0 : ℝ) < ((4 * k ^ (10 * k) : ℕ) : ℝ) := by positivity
  have hraw := (le_div_iff₀ hJ).mp havg
  rw [Fin.sum_univ_eq_sum_range (fun s : ℕ => ‖1 - χ ((s + 1) • u p j a)‖ ^ 2)]
  simpa only [one_mul, ← hsum] using hraw

end TreeEdit.BinaryLower.FiniteVectors

namespace TreeEdit.BinaryLower.FiniteActivity

/-- The exact unnormalized finite-sample detector required by
`finite_tree_spectral_bound`, with the sparse predicate and child list
indices unchanged. All hypotheses are local vector/period identities. -/
theorem characterSparse_detection {α A : Type*}
    [Fintype α] [AddCommGroup A] [Finite A] {k : ℕ}
    (w : List α → A) (v : InternalNode α k) (u : A)
    (Q R : ℕ) (p : α → ℕ) (hk : 1 ≤ k)
    (hQpos : 0 < Q) (hQ : Q ≤ 2 * k ^ (5 * v.1.val))
    (hppos : ∀ i, 0 < p i) (hp : ∀ i, p i ≤ k ^ 5)
    (hroot : w (List.ofFn v.2) = R • u)
    (hsum : u = ∑ i, w (List.ofFn v.2 ++ [i]))
    (hchild : ∀ i, (Q * p i) • w (List.ofFn v.2 ++ [i]) = 0)
    (χ : AddChar A ℂ) (hsparse : characterSparse w k v χ) :
    ((4 * k ^ (10 * k) : ℕ) : ℝ) ≤
      ∑ s : Fin (4 * k ^ (10 * k)), ‖1 - χ ((s.val + 1) • u)‖ ^ 2 := by
  let S : Finset α := Finset.univ.filter fun i => χ (w (List.ofFn v.2 ++ [i])) ≠ 1
  have hcard : S.card < k := by
    simpa only [S, Branching.activeChildCount] using hsparse.2
  have hactive : χ (R • ∑ i, w (List.ofFn v.2 ++ [i])) ≠ 1 := by
    rw [← hsum, ← hroot]
    exact hsparse.1
  have houtside : ∀ i, i ∉ S → χ (w (List.ofFn v.2 ++ [i])) = 1 := by
    intro i hi
    simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hi
  have havg := FinitePeriod.sparse_character_detection χ S
    (fun i => w (List.ofFn v.2 ++ [i])) p hk v.1.isLt hcard hQpos hQ
    (fun i _ => hppos i) (fun i _ => hp i) houtside (fun i _ => hchild i) hactive
  have hJ : (0 : ℝ) < ((4 * k ^ (10 * k) : ℕ) : ℝ) := by positivity
  have hraw := (le_div_iff₀ hJ).mp havg
  rw [Fin.sum_univ_eq_sum_range (fun s : ℕ => ‖1 - χ ((s + 1) • u)‖ ^ 2)]
  simpa only [one_mul, ← hsum] using hraw

end TreeEdit.BinaryLower.FiniteActivity

end

end OAI
