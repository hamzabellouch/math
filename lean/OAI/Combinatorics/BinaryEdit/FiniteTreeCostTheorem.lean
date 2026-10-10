import OAI.Combinatorics.BinaryEdit.FiniteTreeInstantiation
import OAI.Combinatorics.BinaryEdit.FiniteTreeConcreteCosts

namespace OAI

/-!
# The finite tree’s pointwise translation estimates

The concrete `finiteWord` and cyclic-state vectors satisfy `lem:finite-cost`.
Coordinate support follows from the vector definitions.
-/

namespace TreeEdit.BinaryLower.FiniteTree

theorem wordU_off_prefix {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (i₀ : Fin m) (q : List (Fin m)) (hq : q.length ≤ k)
    (l : Leaf m k) (hl : ¬ q.IsPrefix l.val) :
    wordU primes i₀ q l = 0 := by
  change FiniteVectors.u primes q.length (extendPrefix i₀ q) (leafEquiv m k l) = 0
  apply FiniteVectors.u_off_subtree
  intro ha
  have hp := (agrees_extendPrefix_iff i₀ q hq (leafEquiv m k l)).1 ha
  exact hl (by simpa only [ofFn_leafEquiv] using hp)

theorem wordW_off_prefix {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (i₀ : Fin m) (q : List (Fin m)) (hq : q.length ≤ k)
    (l : Leaf m k) (hl : ¬ q.IsPrefix l.val) :
    wordW primes i₀ q l = 0 := by
  change FiniteVectors.w primes q.length (extendPrefix i₀ q) (leafEquiv m k l) = 0
  apply FiniteVectors.w_off_subtree
  intro ha
  have hp := (agrees_extendPrefix_iff i₀ q hq (leafEquiv m k l)).1 ha
  exact hl (by simpa only [ofFn_leafEquiv] using hp)

theorem wordW_leaf_other {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (i₀ : Fin m) (ell l : Leaf m k) (hne : l ≠ ell) :
    wordW primes i₀ ell.val l = 0 := by
  change FiniteVectors.w primes ell.val.length (extendPrefix i₀ ell.val)
    (leafEquiv m k l) = 0
  rw [ell.property, extendPrefix_leaf i₀ ell.val ell.property]
  have hn : leafEquiv m k l ≠ leafEquiv m k ell := by
    intro he
    exact hne ((leafEquiv m k).injective he)
  simp only [FiniteVectors.w_leaf, ite_eq_right hn]

/-- The exact `T^k`-cost script for arbitrary integer changes to a single
cyclic leaf coordinate. The distinguished vector at a leaf is its unit vector. -/
theorem finiteWord_leaf_translation_script {m k : ℕ}
    (primes : Fin k → Fin m → ℕ) (i₀ : Fin m) (T : ℕ)
    (ell : Leaf m k) (t : ℤ) (x : State (wordPeriods primes)) :
    EditScript (finiteWord primes i₀ T k [] x)
      (finiteWord primes i₀ T k [] (x + t • wordW primes i₀ ell.val)) (T ^ k) := by
  apply root_leaf_supported_script T (wordPeriods primes)
    ⟨List.replicate k i₀, by simp⟩ ell (wordU primes i₀)
  intro l hne
  simp only [Pi.smul_apply, wordW_leaf_other primes i₀ ell l hne, smul_zero]

/-- First assertion of `lem:finite-cost`: every state and every integer
multiple of a leaf unit vector has edit cost at most `M/m^k`. -/
theorem finiteWord_leaf_translation_cost {m k : ℕ}
    (primes : Fin k → Fin m → ℕ) (i₀ : Fin m) (T : ℕ)
    (ell : Leaf m k) (t : ℤ) (x : State (wordPeriods primes)) :
    (ed (finiteWord primes i₀ T k [] x)
      (finiteWord primes i₀ T k [] (x + t • wordW primes i₀ ell.val)) : ℝ) ≤
      ((m * T : ℕ) : ℝ) ^ k / (m : ℝ) ^ k := by
  have hm : 0 < m := by have hi := i₀.isLt; omega
  apply root_leaf_supported_normalized_cost T hm (wordPeriods primes)
    ⟨List.replicate k i₀, by simp⟩ ell (wordU primes i₀)
  intro l hne
  simp only [Pi.smul_apply, wordW_leaf_other primes i₀ ell l hne, smul_zero]

/-- An ordinary edit script advances the rows at every occurrence of a node. -/
theorem finiteWord_node_translation_script {m k : ℕ}
    (primes : Fin k → Fin m → ℕ) (i₀ : Fin m) (T : ℕ)
    (q : List (Fin m)) (hq : q.length < k)
    (s : ℕ) (hs : s ≤ T) (x : State (wordPeriods primes)) :
    EditScript (finiteWord primes i₀ T k [] x)
      (finiteWord primes i₀ T k [] (x + s • wordU primes i₀ q))
      (T ^ q.length * (2 * s * m * (m * T) ^ (k - (q.length + 1)))) := by
  apply root_internal_supported_script T (wordPeriods primes)
    ⟨List.replicate k i₀, by simp⟩ (wordU primes i₀) (k - (q.length + 1)) q
    (by omega) s hs
  exact wordU_off_prefix primes i₀ q hq.le

/-- Equation `eq:finite-cost` with the concrete root word, actual cheap
vector, and exact source constants. It holds uniformly at every state and
also includes the harmless zero shift. -/
theorem finiteWord_node_translation_cost {m k : ℕ}
    (primes : Fin k → Fin m → ℕ) (i₀ : Fin m) (T : ℕ) (hT : 0 < T)
    (q : List (Fin m)) (hq : q.length < k)
    (s : ℕ) (hs : s ≤ T) (x : State (wordPeriods primes)) :
    (ed (finiteWord primes i₀ T k [] x)
      (finiteWord primes i₀ T k [] (x + s • wordU primes i₀ q)) : ℝ) ≤
      (2 * (s : ℝ) / T) * (((m * T : ℕ) : ℝ) ^ k / (m : ℝ) ^ q.length) := by
  have hm : 0 < m := by have hi := i₀.isLt; omega
  apply root_internal_supported_normalized_cost T hm hT (wordPeriods primes)
    ⟨List.replicate k i₀, by simp⟩ (wordU primes i₀) (k - (q.length + 1)) q
    (by omega) s hs
  exact wordU_off_prefix primes i₀ q hq.le

end TreeEdit.BinaryLower.FiniteTree

end OAI
