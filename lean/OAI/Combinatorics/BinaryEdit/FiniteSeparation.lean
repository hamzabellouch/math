import OAI.Combinatorics.BinaryEdit.FiniteTreeInstantiation
import OAI.Combinatorics.BinaryEdit.FiniteWordPrimeSeparation
import OAI.Combinatorics.BinaryEdit.FiniteTreeTags
import OAI.Combinatorics.BinaryEdit.FiniteSeparationArithmetic
import OAI.Combinatorics.BinaryEdit.TaggedArrays

namespace OAI

/-!
# Geometric separation for the concrete finite tree

The prime construction supplies the half-child condition in the
geometric induction.
-/

noncomputable section
namespace TreeEdit.BinaryLower.FiniteTree

open scoped BigOperators

/-- Literal row/block array of a concrete node word. -/
def finiteBlocks {m k : ℕ} (primes : Fin k → Fin m → ℕ) (i₀ : Fin m)
    (T h : ℕ) (p : List (Fin m)) (x : State (wordPeriods primes)) :
    Fin T → Fin m → Word (Symbol (wordPeriods primes)) ((m * T) ^ h) :=
  fun a i => ⟨finiteWord primes i₀ T h (p ++ [i]) (x + a.val • wordU primes i₀ p),
    finiteWord_length primes i₀ T h _ _⟩

theorem finiteWord_succ_eq_rows {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (i₀ : Fin m) (T h : ℕ) (p : List (Fin m)) (x : State (wordPeriods primes)) :
    finiteWord primes i₀ T (h + 1) p x =
      TaggedExtraction.rows (finiteBlocks primes i₀ T h p x) := by
  have hrange : (List.finRange T).map Fin.val = List.range T := by
    apply List.ext_getElem
    · simp
    · intro j hj hj'
      simp
  unfold finiteWord nodeWord
  rw [← hrange, List.flatMap_map]
  rfl

/-- The relative coefficient comparing two rows in a child. -/
def finiteRowShift {m k T : ℕ} (primes : Fin k → Fin m → ℕ)
    (p : List (Fin m)) (hp : p.length < k) (a b : Fin T) (t : ℤ) : ℤ :=
  (b.val : ℤ) - (a.val : ℤ) + t *
    (FiniteVectors.levelProduct primes ⟨p.length, hp⟩ : ℤ)

/-- Children whose prescribed period does not divide the relative coefficient. -/
def separatedChildren {m k T : ℕ} (primes : Fin k → Fin m → ℕ)
    (i₀ : Fin m) (p : List (Fin m)) (hp : p.length < k) (a b : Fin T) (t : ℤ) :
    Finset (Fin m) :=
  Finset.univ.filter fun i => ¬ (wordPeriod primes i₀ (p ++ [i]) : ℤ) ∣
    finiteRowShift primes p hp a b t

/-- Ordered-tag alignment and half-child nondivisibility imply separation
for arbitrary common-subsequence matchings. -/
theorem finiteWord_separation_of_half_children {m k T : ℕ}
    (primes : Fin k → Fin m → ℕ) (i₀ : Fin m) (hm : 2 ≤ m) (hT : 0 < T)
    (hhalf : ∀ p (hp : p.length < k) (a b : Fin T) (t : ℤ),
      ¬ (wordPeriod primes i₀ p : ℤ) ∣ t →
      m ≤ 2 * (separatedChildren primes i₀ p hp a b t).card)
    (h : ℕ) (p : List (Fin m)) (hlen : p.length + h = k)
    (x : State (wordPeriods primes)) (t : ℤ)
    (ht : ¬ (wordPeriod primes i₀ p : ℤ) ∣ t) :
    (((m * T) ^ h : ℕ) : ℝ) / (4 : ℝ) ^ h ≤
      (deficit ((m * T) ^ h) (finiteWord primes i₀ T h p x)
        (finiteWord primes i₀ T h p (x + t • wordW primes i₀ p)) : ℝ) := by
  classical
  induction h generalizing p x t with
  | zero =>
      have hp : p.length = k := by simpa using hlen
      simpa using (finiteWord_leaf_deficit primes i₀ T p hp x t ht).symm.le
  | succ h ih =>
      have hp : p.length < k := by omega
      let B : ℕ := (m * T) ^ h
      let q : ℝ := (B : ℝ) / (4 : ℝ) ^ h
      let d : ℝ := (m : ℝ) * q / 2
      let X := finiteBlocks primes i₀ T h p x
      let Y := finiteBlocks primes i₀ T h p (x + t • wordW primes i₀ p)
      have hB : 0 < B := by dsimp [B]; exact pow_pos (Nat.mul_pos (by omega) hT) _
      have hq : 0 ≤ q := by dsimp [q]; positivity
      have hd : 0 ≤ d := by dsimp [d]; positivity
      have hlocal (a b : Fin T) : d ≤ ∑ i, (deficit B (X a i).val (Y b i).val : ℝ) := by
        apply row_deficit_charge (separatedChildren primes i₀ p hp a b t) _ q hq
          (fun i => Nat.cast_nonneg _) _ (hhalf p hp a b t ht)
        intro i hi
        have hnot : ¬ (wordPeriod primes i₀ (p ++ [i]) : ℤ) ∣
            finiteRowShift primes p hp a b t := (Finset.mem_filter.mp hi).2
        change q ≤ (deficit B
          (finiteWord primes i₀ T h (p ++ [i]) (x + a.val • wordU primes i₀ p))
          (finiteWord primes i₀ T h (p ++ [i])
            (x + t • wordW primes i₀ p + b.val • wordU primes i₀ p)) : ℝ)
        rw [finiteWord_child_relative primes i₀ i T h p hlen x t a.val b.val]
        exact ih (p ++ [i]) (by simp; omega) _ _ hnot
      have hX : ∀ (a : Fin T) (i : Fin m) (s : Symbol (wordPeriods primes)),
          s ∈ (X a i).val → s ∈ subtreeAlphabet (wordPeriods primes) (p ++ [i]) := by
        intro a i s hs
        exact mem_subtreeAlphabet_of_mem (wordPeriods primes)
          ⟨List.replicate k i₀, by simp⟩ (wordU primes i₀) h (p ++ [i])
          (by simp; omega) _ s hs
      have hY : ∀ (a : Fin T) (i : Fin m) (s : Symbol (wordPeriods primes)),
          s ∈ (Y a i).val → s ∈ subtreeAlphabet (wordPeriods primes) (p ++ [i]) := by
        intro a i s hs
        exact mem_subtreeAlphabet_of_mem (wordPeriods primes)
          ⟨List.replicate k i₀, by simp⟩ (wordU primes i₀) h (p ++ [i])
          (by simp; omega) _ s hs
      have hdg : d ≤ (((m - 1) * B : ℕ) : ℝ) := by
        have hh := finite_charge_le_gap m h hm (B : ℝ) (Nat.cast_nonneg _)
        simpa [d, q, Nat.cast_mul, Nat.cast_sub (show 1 ≤ m by omega)] using hh
      have hsep := (Tagged.rows_with_ordered_tags hT hm hB
        (fun i => subtreeAlphabet (wordPeriods primes) (p ++ [i]))
        (subtreeAlphabet_children_pairwise_disjoint (wordPeriods primes) p)
        X Y hX hY d hd hlocal).2.2 hdg
      have hN : T * m * B = (m * T) ^ (h + 1) := by dsimp [B]; rw [pow_succ]; ring
      have hcharge : (T : ℝ) * d / 2 = (((m * T) ^ (h + 1) : ℕ) : ℝ) / (4 : ℝ) ^ (h + 1) := by
        dsimp [d, q, B]
        push_cast
        rw [pow_succ, pow_succ]
        ring
      rw [hcharge, hN] at hsep
      simpa only [X, Y, ← finiteWord_succ_eq_rows] using hsep

/-- Uniform separation of the root half-period shift. -/
theorem finiteWord_root_deficit_of_half_children {m k T : ℕ}
    (primes : Fin k → Fin m → ℕ) (i₀ : Fin m) (hm : 2 ≤ m) (hT : 0 < T)
    (hhalf : ∀ p (hp : p.length < k) (a b : Fin T) (t : ℤ),
      ¬ (wordPeriod primes i₀ p : ℤ) ∣ t →
      m ≤ 2 * (separatedChildren primes i₀ p hp a b t).card)
    (x : State (wordPeriods primes)) :
    (((m * T) ^ k : ℕ) : ℝ) / (4 : ℝ) ^ k ≤
      (deficit ((m * T) ^ k) (finiteWord primes i₀ T k [] x)
        (finiteWord primes i₀ T k [] (x + wordW primes i₀ [])) : ℝ) := by
  have h := finiteWord_separation_of_half_children primes i₀ hm hT hhalf
    k [] (by simp) x 1 (by simp)
  simpa using h

/-- Source finite-tree separation for the actual prime periods and words. -/
theorem finiteWord_separation {k : ℕ} (hk : 2 ≤ k)
    (primes : Fin k → Fin (20 * k) → ℕ) (i₀ : Fin (20 * k))
    (hinj : Function.Injective
      (fun z : Fin k × Fin (20 * k) => primes z.1 z.2))
    (hprime : ∀ q i, Nat.Prime (primes q i))
    (hlarge : ∀ q i, k ^ 4 ≤ primes q i)
    (h : ℕ) (p : List (Fin (20 * k))) (hlen : p.length + h = k)
    (x : State (wordPeriods primes)) (t : ℤ)
    (ht : ¬ (wordPeriod primes i₀ p : ℤ) ∣ t) :
    (((20 * k * k ^ (20 * k)) ^ h : ℕ) : ℝ) / (4 : ℝ) ^ h ≤
      (deficit ((20 * k * k ^ (20 * k)) ^ h)
        (finiteWord primes i₀ (k ^ (20 * k)) h p x)
        (finiteWord primes i₀ (k ^ (20 * k)) h p
          (x + t • wordW primes i₀ p)) : ℝ) := by
  apply finiteWord_separation_of_half_children primes i₀ (by omega)
    (pow_pos (by omega) _) _ h p hlen x t ht
  intro p hp a b t ht
  exact finiteWord_half_children hk primes i₀ p hp hinj hprime hlarge a b t ht

/-- Distinct large primes give the uniform root deficit for the
prescribed half-period shift. -/
theorem finiteWord_root_deficit {k : ℕ} (hk : 2 ≤ k)
    (primes : Fin k → Fin (20 * k) → ℕ) (i₀ : Fin (20 * k))
    (hinj : Function.Injective
      (fun z : Fin k × Fin (20 * k) => primes z.1 z.2))
    (hprime : ∀ q i, Nat.Prime (primes q i))
    (hlarge : ∀ q i, k ^ 4 ≤ primes q i)
    (x : State (wordPeriods primes)) :
    (((20 * k * k ^ (20 * k)) ^ k : ℕ) : ℝ) / (4 : ℝ) ^ k ≤
      (deficit ((20 * k * k ^ (20 * k)) ^ k)
        (finiteWord primes i₀ (k ^ (20 * k)) k [] x)
        (finiteWord primes i₀ (k ^ (20 * k)) k []
          (x + wordW primes i₀ [])) : ℝ) := by
  have h := finiteWord_separation hk primes i₀ hinj hprime hlarge k []
    (by simp) x 1 (by simp)
  simpa using h

end TreeEdit.BinaryLower.FiniteTree

end

end OAI
