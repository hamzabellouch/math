import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticSplitData

namespace OAI

/-! # Multiplying the actual split probabilities at fixed frequencies -/

namespace Ostmann

open scoped BigOperators Classical

structure NodeFrequencies where
  root : ℤ
  left : ℤ
  right : ℤ

def NodeFrequencies.reducedModulus (f : NodeFrequencies) : ℕ :=
  reducedFrequency (f.left.natAbs.gcd f.right.natAbs) f.root.natAbs

def ArithmeticSplitData.hasFrequencies {Q : ℕ} (d : ArithmeticSplitData Q)
    (f : NodeFrequencies) : Prop :=
  d.frequency = f.root ∧ d.leftFrequency = f.left ∧ d.rightFrequency = f.right

theorem ArithmeticSplitData.reducedModulus_eq {Q : ℕ} (d : ArithmeticSplitData Q)
    (f : NodeFrequencies) (h : d.hasFrequencies f) : d.reducedModulus = f.reducedModulus := by
  simp only [ArithmeticSplitData.reducedModulus, NodeFrequencies.reducedModulus, h.1, h.2.1, h.2.2]

noncomputable def pairFrequencySupportBound (D : ℝ) (f : NodeFrequencies × NodeFrequencies) : ℝ :=
  2 * D ^ 2 / f.1.reducedModulus.lcm f.2.reducedModulus

theorem pairFrequencySupportBound_nonneg (D : ℝ) (f : NodeFrequencies × NodeFrequencies) :
    0 ≤ pairFrequencySupportBound D f := by unfold pairFrequencySupportBound; positivity

/-- The reduced moduli depend only on the fixed frequencies. All pivot
and unit data may still vary with the previously exposed split products. -/
theorem arithmetic_support_fixed_frequencies {Q : ℕ} [NeZero Q]
    (data : List (ZMod Q)ˣ → Option (ArithmeticSplitData Q × ArithmeticSplitData Q))
    (frequencies : ℕ → NodeFrequencies × NodeFrequencies) (D : ℝ) (_hD : 0 ≤ D)
    (hmatch : ∀ past d e, data past = some (d, e) →
      d.hasFrequencies (frequencies past.length).1 ∧
        e.hasFrequencies (frequencies past.length).2)
    (hdiv : ∀ j, (((frequencies j).1.reducedModulus.lcm
      (frequencies j).2.reducedModulus).divisors.card : ℝ) ≤ D)
    (n : ℕ) :
    (Fintype.card (ZMod Q)ˣ : ℝ)⁻¹ ^ n *
        (∑ x : SplitSamples (ZMod Q)ˣ n,
          sequentialSupport (fun past y => arithmeticPairSplitTest (data past) y) [] n x) ≤
      ∏ j ∈ Finset.range n, pairFrequencySupportBound D (frequencies j) := by
  apply arithmetic_sequential_support_le data _ (fun _ => pairFrequencySupportBound_nonneg _ _) _ n
  intro past d e hd
  obtain ⟨hdmatch, hematch⟩ := hmatch past d e hd
  rw [d.reducedModulus_eq _ hdmatch, e.reducedModulus_eq _ hematch]
  unfold pairFrequencySupportBound
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Nat.cast_nonneg _) (hdiv past.length) 2) (by norm_num)

/-- The same product estimate on the original uniformly sampled leaf
tuples, conditional only on their total product. -/
theorem arithmetic_leaf_support_fixed_frequencies {Q : ℕ} [NeZero Q]
    (data : List (ZMod Q)ˣ → Option (ArithmeticSplitData Q × ArithmeticSplitData Q))
    (frequencies : ℕ → NodeFrequencies × NodeFrequencies) (D : ℝ) (hD : 0 ≤ D)
    (hmatch : ∀ past d e, data past = some (d, e) →
      d.hasFrequencies (frequencies past.length).1 ∧
        e.hasFrequencies (frequencies past.length).2)
    (hdiv : ∀ j, (((frequencies j).1.reducedModulus.lcm
      (frequencies j).2.reducedModulus).divisors.card : ℝ) ≤ D)
    (n : ℕ) (P : (ZMod Q)ˣ) :
    (Fintype.card (TreeLeafFiber (ZMod Q)ˣ n P) : ℝ)⁻¹ *
        (∑ x : TreeLeafFiber (ZMod Q)ˣ n P,
          sequentialSupport (fun past y => arithmeticPairSplitTest (data past) y) []
            (2 ^ n - 1) (treeLeafSplitEquiv n P x)) ≤
      ∏ j ∈ Finset.range (2 ^ n - 1), pairFrequencySupportBound D (frequencies j) := by
  rw [treeLeafSplit_average]
  exact arithmetic_support_fixed_frequencies data frequencies D hD hmatch hdiv (2 ^ n - 1)

end Ostmann

end OAI
