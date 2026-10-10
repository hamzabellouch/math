import OAI.Combinatorics.BinaryEdit.FiniteTreeInstantiation
import OAI.Combinatorics.BinaryEdit.FiniteVectorDetection
import OAI.Combinatorics.BinaryEdit.WordFinite
import OAI.Combinatorics.BinaryEdit.FiniteCoordinates

namespace OAI

/-!
# Sparse detection for the concrete recursive word model

The list-prefix vectors used by `finiteWord` satisfy the same exact recursion
and period bounds as the function-prefix vectors. This closes the algebraic
inputs of the finite spectral detector in the actual word-state presentation.
-/

noncomputable section

open scoped BigOperators
open Classical

namespace TreeEdit.BinaryLower.FiniteTree

variable {m k : ℕ}

theorem wordState_finite (primes : Fin k → Fin m → ℕ)
    (hp : ∀ q i, 0 < primes q i) : Finite (State (wordPeriods primes)) := by
  let : ∀ l : Leaf m k, NeZero (wordPeriods primes l) := fun l =>
    ⟨ne_of_gt (FiniteVectors.leafPeriod_pos primes hp (leafEquiv m k l))⟩
  infer_instance

/-- Relabeling the product factors is additive, not merely a map of sets. -/
def pullStateHom (Q : (Fin k → Fin m) → ℕ) :
    (∀ l, ZMod (Q l)) →+ State (fun l => Q (leafEquiv m k l)) where
  toFun := pullState Q
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The actual word-state cyclic coordinate, indexed by the same function
leaves as the spectral tree's finite leaf set. -/
def wordLeafCoordinate (primes : Fin k → Fin m → ℕ) (f : Fin k → Fin m) :
    ZMod (FiniteVectors.leafPeriod primes f) →+ State (wordPeriods primes) :=
  (pullStateHom (FiniteVectors.leafPeriod primes)).comp
    (FiniteVectors.leafCoordinate primes f)

@[simp] theorem extendPrefix_ofFn (i₀ : Fin m) (f : Fin k → Fin m) :
    extendPrefix i₀ (List.ofFn f) = f := by
  funext q
  simp [extendPrefix, q.isLt]

/-- This is precisely the generator identity of the spectral tree theorem. -/
@[simp] theorem wordLeafCoordinate_one (primes : Fin k → Fin m → ℕ)
    (i₀ : Fin m) (f : Fin k → Fin m) :
    wordLeafCoordinate primes f 1 = wordW primes i₀ (List.ofFn f) := by
  change pullState (FiniteVectors.leafPeriod primes)
    (FiniteVectors.leafCoordinate primes f 1) = _
  rw [FiniteVectors.leafCoordinate_one]
  simp only [wordW, List.length_ofFn, extendPrefix_ofFn]

/-- Whole-coordinate averaging uses only integer multiples of the actual
word leaf vector, as in the pointwise inexpensive-leaf-translation lemma. -/
theorem wordLeafCoordinate_eq_val_zsmul (primes : Fin k → Fin m → ℕ)
    (i₀ : Fin m) (f : Fin k → Fin m)
    [NeZero (FiniteVectors.leafPeriod primes f)]
    (z : ZMod (FiniteVectors.leafPeriod primes f)) :
    wordLeafCoordinate primes f z = (z.val : ℤ) • wordW primes i₀ (List.ofFn f) := by
  have hz : (z.val : ℤ) • (1 : ZMod (FiniteVectors.leafPeriod primes f)) = z := by
    simp
  calc
    wordLeafCoordinate primes f z = wordLeafCoordinate primes f ((z.val : ℤ) • 1) :=
      congrArg _ hz.symm
    _ = (z.val : ℤ) • wordLeafCoordinate primes f 1 := map_zsmul _ _ _
    _ = (z.val : ℤ) • wordW primes i₀ (List.ofFn f) := by rw [wordLeafCoordinate_one primes i₀]

theorem wordPeriod_pos (primes : Fin k → Fin m → ℕ)
    (hp : ∀ q i, 0 < primes q i) (i₀ : Fin m) (p : List (Fin m)) :
    0 < wordPeriod primes i₀ p :=
  FiniteVectors.prefixPeriod_pos primes hp p.length (extendPrefix i₀ p)

theorem wordPeriod_le (primes : Fin k → Fin m → ℕ)
    (hp : ∀ q i, primes q i ≤ k ^ 5) (i₀ : Fin m) (p : List (Fin m))
    (hlen : p.length ≤ k) : wordPeriod primes i₀ p ≤ 2 * k ^ (5 * p.length) :=
  FiniteVectors.prefixPeriod_le primes hp p.length hlen (extendPrefix i₀ p)

theorem wordPeriod_child (primes : Fin k → Fin m → ℕ)
    (i₀ i : Fin m) (p : List (Fin m)) (hp : p.length < k) :
    wordPeriod primes i₀ (p ++ [i]) =
      wordPeriod primes i₀ p * primes ⟨p.length, hp⟩ i := by
  simp only [wordPeriod, List.length_append, List.length_singleton,
    extendPrefix_append i₀ i p hp]
  exact FiniteVectors.prefixPeriod_child primes p.length hp (extendPrefix i₀ p) i

/-- The distinguished word-state vector is the level product times the
actual cheap word-state vector. -/
theorem wordW_eq_level_nsmul_wordU (primes : Fin k → Fin m → ℕ)
    (i₀ : Fin m) (p : List (Fin m)) (hp : p.length < k) :
    wordW primes i₀ p = FiniteVectors.levelProduct primes ⟨p.length, hp⟩ •
      wordU primes i₀ p := by
  unfold wordW wordU
  rw [FiniteVectors.w_eq_level_nsmul_u primes p.length hp (extendPrefix i₀ p)]
  rfl

/-- The cheap word-state vector is exactly the sum of the children's
distinguished vectors, with the same list indices used for branching. -/
theorem wordU_eq_sum_child_wordW (primes : Fin k → Fin m → ℕ)
    (i₀ : Fin m) (p : List (Fin m)) (hp : p.length < k) :
    wordU primes i₀ p = ∑ i : Fin m, wordW primes i₀ (p ++ [i]) := by
  unfold wordU wordW wordPeriods
  simp only [List.length_append, List.length_singleton, extendPrefix_append i₀ _ p hp]
  rw [FiniteVectors.u_eq_sum_child_w primes p.length hp (extendPrefix i₀ p)]
  funext l
  simp only [pullState, Finset.sum_apply]

/-- A sparse active node is detected by short averages of cheap shifts
in the canonical word-state group. -/
theorem word_sparse_detection (primes : Fin k → Fin m → ℕ) (i₀ : Fin m)
    (hk : 1 ≤ k) (hppos : ∀ q i, 0 < primes q i)
    (hp : ∀ q i, primes q i ≤ k ^ 5)
    (v : FiniteActivity.InternalNode (Fin m) k)
    (χ : AddChar (State (wordPeriods primes)) ℂ)
    (hsparse : FiniteActivity.characterSparse (wordW primes i₀) k v χ) :
    ((4 * k ^ (10 * k) : ℕ) : ℝ) ≤
      ∑ s : Fin (4 * k ^ (10 * k)),
        ‖1 - χ ((s.val + 1) • wordU primes i₀ (List.ofFn v.2))‖ ^ 2 := by
  let : Finite (State (wordPeriods primes)) := wordState_finite primes hppos
  let p := List.ofFn v.2
  have hlen : p.length < k := by simp [p]
  apply FiniteActivity.characterSparse_detection (wordW primes i₀) v
    (wordU primes i₀ p) (wordPeriod primes i₀ p)
    (FiniteVectors.levelProduct primes ⟨p.length, hlen⟩)
    (primes ⟨p.length, hlen⟩) hk
  · exact wordPeriod_pos primes hppos i₀ p
  · simpa [p] using wordPeriod_le primes hp i₀ p hlen.le
  · exact hppos _
  · exact hp _
  · exact wordW_eq_level_nsmul_wordU primes i₀ p hlen
  · exact wordU_eq_sum_child_wordW primes i₀ p hlen
  · intro i
    rw [← wordPeriod_child primes i₀ i p hlen]
    exact wordPeriod_nsmul_wordW primes i₀ (p ++ [i])
  · exact hsparse

end TreeEdit.BinaryLower.FiniteTree

end

end OAI
