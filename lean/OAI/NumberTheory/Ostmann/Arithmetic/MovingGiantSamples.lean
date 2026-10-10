import OAI.NumberTheory.Ostmann.Arithmetic.MovingGiantTree
import OAI.NumberTheory.Ostmann.Construction.WordTransferFullPeriod

namespace OAI

/-! # Constructing the moving-giant tree from the sampled compensation slots

Each reversing node samples four positions per leaf of either child. Their
products are inserted into both child regular lists. The constructor proves
the required product consistency; it does not ask for a pre-existing diagram.
-/

namespace Ostmann
open scoped BigOperators

/-- The four actual compensation positions per child leaf at a reversal. -/
inductive MovingGiantSamples : ℕ → Type
  | leaf : MovingGiantSamples 0
  | node {n : ℕ} (samples : TreeLeafTuple (Fin 4 → ℕ) n)
      (left right : MovingGiantSamples n) : MovingGiantSamples (n + 1)

def compensationLeafProducts : (n : ℕ) →
    TreeLeafTuple (Fin 4 → ℕ) n → TreeLeafTuple ℕ n
  | 0, x => (∏ i : Fin 4, (show Fin 4 → ℕ from x) i : ℕ)
  | n + 1, x => (compensationLeafProducts n x.1, compensationLeafProducts n x.2)

def multiplySmallLeaves : (n : ℕ) →
    TreeLeafTuple ℕ n → TreeLeafTuple ℕ n → TreeLeafTuple ℕ n
  | 0, x, y => (show ℕ from x) * (show ℕ from y)
  | n + 1, x, y => (multiplySmallLeaves n x.1 y.1, multiplySmallLeaves n x.2 y.2)

theorem multiplySmallLeaves_product (n : ℕ) (x y : TreeLeafTuple ℕ n) :
    treeLeafProduct n (multiplySmallLeaves n x y) = treeLeafProduct n x * treeLeafProduct n y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [multiplySmallLeaves, treeLeafProduct, ih]
    ring

def MovingGiantTree.castConstant {n C D : ℕ} (h : C = D)
    (T : MovingGiantTree n C) : MovingGiantTree n D := h ▸ T

@[simp] theorem MovingGiantTree.castConstant_frequency {n C D : ℕ} (h : C = D)
    (T : MovingGiantTree n C) : (T.castConstant h).frequency = T.frequency := by
  subst D
  rfl

@[simp] theorem MovingGiantTree.castConstant_units {n C D : ℕ} (h : C = D)
    (T : MovingGiantTree n C) (q : ℕ) : (T.castConstant h).UnitsAt q ↔ T.UnitsAt q := by
  subst D
  rfl

/-- `small` contains only the fixed regular factors at the top of this history.
Bulk values and the two moving giants do not occur in this constructor. -/
def buildMovingGiantTree : (n : ℕ) → (t : FrequencyTree ℤ n) →
    (small : TreeLeafTuple ℕ n) → MovingGiantSamples n →
      MovingGiantTree n (treeLeafProduct n small)
  | 0, t, small, .leaf => .leaf (frequencyRoot 0 t) (treeLeafProduct 0 small)
  | n + 1, t, small, .node samples left right =>
      let u := compensationLeafProducts n samples
      let L := buildMovingGiantTree n t.2.1 (multiplySmallLeaves n u small.1) left
      let R := buildMovingGiantTree n t.2.2 (multiplySmallLeaves n u small.2) right
      .node t.1 (treeLeafProduct n small.1) (treeLeafProduct n small.2) (treeLeafProduct n u)
        (L.castConstant (multiplySmallLeaves_product n u small.1))
        (R.castConstant (multiplySmallLeaves_product n u small.2))

theorem buildMovingGiantTree_frequency (n : ℕ) (t : FrequencyTree ℤ n)
    (small : TreeLeafTuple ℕ n) (samples : MovingGiantSamples n) :
    (buildMovingGiantTree n t small samples).frequency = frequencyRoot n t := by
  cases samples <;> rfl

def movingGiantFrequencyUnits (q : ℕ) : (n : ℕ) → FrequencyTree ℤ n → Prop
  | 0, t => ((frequencyRoot 0 t : ℤ) : ZMod q) ≠ 0
  | n + 1, t => (t.1 : ZMod q) ≠ 0 ∧
      movingGiantFrequencyUnits q n t.2.1 ∧ movingGiantFrequencyUnits q n t.2.2

def MovingGiantSamples.UnitsAt (q : ℕ) : {n : ℕ} → MovingGiantSamples n → Prop
  | _, .leaf => True
  | n + 1, .node samples left right =>
      ((treeLeafProduct n (compensationLeafProducts n samples) : ℕ) : ZMod q) ≠ 0 ∧
      left.UnitsAt q ∧ right.UnitsAt q

/-- Unit conditions for the diagram follow from the actual sampled products
and original frequency bounds. They are independent of the bulk variables. -/
theorem buildMovingGiantTree_units {q n : ℕ} [Fact q.Prime] (t : FrequencyTree ℤ n)
    (small : TreeLeafTuple ℕ n) (samples : MovingGiantSamples n)
    (hfreq : movingGiantFrequencyUnits q n t)
    (hsmall : ((treeLeafProduct n small : ℕ) : ZMod q) ≠ 0)
    (hsamples : samples.UnitsAt q) :
    (buildMovingGiantTree n t small samples).UnitsAt q := by
  induction samples with
  | leaf => exact ⟨hfreq, hsmall⟩
  | @node n samples left right ihL ihR =>
    have hparts : ((treeLeafProduct n small.1 : ℕ) : ZMod q) ≠ 0 ∧
        ((treeLeafProduct n small.2 : ℕ) : ZMod q) ≠ 0 := by
      simpa only [treeLeafProduct, Nat.cast_mul, mul_ne_zero_iff] using hsmall
    refine ⟨hfreq.1, hparts.1, hparts.2, hsamples.1, ?_, ?_⟩
    · rw [MovingGiantTree.castConstant_units]
      apply ihL _ _ hfreq.2.1 _ hsamples.2.1
      rw [multiplySmallLeaves_product, Nat.cast_mul]
      exact mul_ne_zero hsamples.1 hparts.1
    · rw [MovingGiantTree.castConstant_units]
      apply ihR _ _ hfreq.2.2 _ hsamples.2.2
      rw [multiplySmallLeaves_product, Nat.cast_mul]
      exact mul_ne_zero hsamples.1 hparts.2

theorem movingGiantFrequencyUnits_of_bounds {q n : ℕ} [Fact q.Prime]
    (t : FrequencyTree ℤ n)
    (h : ∀ s ∈ allFrequencyList n t, s ≠ 0 ∧ s.natAbs < q) :
    movingGiantFrequencyUnits q n t := by
  induction n with
  | zero =>
    have hs := h (frequencyRoot 0 t) (by simp [allFrequencyList, frequencyRoot])
    exact spectator_frequency_ne_zero _ hs.1 hs.2
  | succ n ih =>
    refine ⟨spectator_frequency_ne_zero _ (h t.1 (by simp [allFrequencyList])).1
      (h t.1 (by simp [allFrequencyList])).2, ?_, ?_⟩
    · apply ih t.2.1
      intro s hs
      exact h s (List.mem_cons_of_mem _ (List.mem_append_left _ hs))
    · apply ih t.2.2
      intro s hs
      exact h s (List.mem_cons_of_mem _ (List.mem_append_right _ hs))

def MovingGiantSamples.sampleCount : {n : ℕ} → MovingGiantSamples n → ℕ
  | _, .leaf => 0
  | n + 1, .node _ left right => 4 * 2 ^ n + left.sampleCount + right.sampleCount

/-- The literal internal sample count is the `O(k r)` count in Section 8.1. -/
theorem MovingGiantSamples.sampleCount_eq {n : ℕ} (samples : MovingGiantSamples n) :
    samples.sampleCount = 2 * n * 2 ^ n := by
  induction samples with
  | leaf => rfl
  | @node n samples left right ihL ihR =>
    simp only [sampleCount, ihL, ihR, pow_succ]
    ring

end Ostmann

end OAI
