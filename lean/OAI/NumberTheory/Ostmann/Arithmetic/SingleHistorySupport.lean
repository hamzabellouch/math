import OAI.NumberTheory.Ostmann.Arithmetic.SingleFrequencyTree
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticHistorySupportSum
import OAI.NumberTheory.Ostmann.Characters.TreeProductDisintegration

namespace OAI

/-! # Exact one-history arithmetic support under independent uniform leaves -/

namespace Ostmann

open scoped BigOperators Classical

def diagonalSplitData {Q : ℕ} (d : Option (ArithmeticSplitData Q)) :
    Option (ArithmeticSplitData Q × ArithmeticSplitData Q) := d.map fun e => (e, e)

def singleArithmeticSplitTest {Q : ℕ} (d : Option (ArithmeticSplitData Q))
    (x : (ZMod Q)ˣ) : Prop := match d with
  | none => False
  | some e => e.test x

theorem diagonalSplitData_test {Q : ℕ} (d : Option (ArithmeticSplitData Q))
    (x : (ZMod Q)ˣ) :
    arithmeticPairSplitTest (diagonalSplitData d) x ↔ singleArithmeticSplitTest d x := by
  cases d <;> simp [diagonalSplitData, arithmeticPairSplitTest, singleArithmeticSplitTest]

noncomputable def singleArithmeticLeafSupport {Q : ℕ} [NeZero Q]
    (n : ℕ) (data : (ZMod Q)ˣ → List (ZMod Q)ˣ → Option (ArithmeticSplitData Q))
    (x : TreeLeafTuple (ZMod Q)ˣ n) : ℝ :=
  sequentialSupport (fun past y => singleArithmeticSplitTest (data (treeLeafProduct n x) past) y)
    [] (2 ^ n - 1) (treeLeafSplitEquiv n (treeLeafProduct n x) ⟨x, rfl⟩)

theorem singleArithmeticLeafSupport_nonneg {Q : ℕ} [NeZero Q]
    (n : ℕ) (data : (ZMod Q)ˣ → List (ZMod Q)ˣ → Option (ArithmeticSplitData Q))
    (x : TreeLeafTuple (ZMod Q)ˣ n) : 0 ≤ singleArithmeticLeafSupport n data x :=
  sequentialSupport_nonneg _ _ _ _

/-- The already proved joint root bound, applied twice to the same test,
loses no additional frequency choices or support conditions. -/
theorem single_arithmetic_leaf_support_le {Q : ℕ} [NeZero Q]
    (data : List (ZMod Q)ˣ → Option (ArithmeticSplitData Q))
    (frequencies : ℕ → NodeFrequencies) (D : ℝ) (hD : 0 ≤ D)
    (hmatch : ∀ past d, data past = some d → d.hasFrequencies (frequencies past.length))
    (hdiv : ∀ j, ((frequencies j).reducedModulus.divisors.card : ℝ) ≤ D)
    (n : ℕ) (P : (ZMod Q)ˣ) :
    (Fintype.card (TreeLeafFiber (ZMod Q)ˣ n P) : ℝ)⁻¹ *
      (∑ x : TreeLeafFiber (ZMod Q)ˣ n P,
        sequentialSupport (fun past y => singleArithmeticSplitTest (data past) y) []
          (2 ^ n - 1) (treeLeafSplitEquiv n P x)) ≤
      ∏ j ∈ Finset.range (2 ^ n - 1), singleFrequencySupportBound D (frequencies j) := by
  have hm : ∀ past d e, diagonalSplitData (data past) = some (d, e) →
      d.hasFrequencies (frequencies past.length) ∧
      e.hasFrequencies (frequencies past.length) := by
    intro past d e he
    cases hd : data past with
    | none => simp [diagonalSplitData, hd] at he
    | some f =>
      have heq : (f, f) = (d, e) := by simpa [diagonalSplitData, hd] using he
      have hf := hmatch past f hd
      cases heq
      exact ⟨hf, hf⟩
  have hb := arithmetic_leaf_support_fixed_frequencies
    (fun past => diagonalSplitData (data past)) (fun j => (frequencies j, frequencies j)) D hD hm
    (fun j => by simpa only [Nat.lcm_self] using hdiv j) n P
  simpa only [diagonalSplitData_test, pairFrequencySupportBound, Nat.lcm_self,
    singleFrequencySupportBound] using hb

/-- Pointwise in the frequency history and independent of the size of Q.
This permits the modulus to be chosen separately for each history. -/
theorem single_arithmetic_leaf_average_le {Q : ℕ} [NeZero Q]
    (S : Finset ℤ) (N n : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D)
    (t : FrequencyTree S n)
    (data : (ZMod Q)ˣ → List (ZMod Q)ˣ → Option (ArithmeticSplitData Q))
    (hmatch : ∀ P past d, data P past = some d →
      d.hasFrequencies (singleTreeNodeFrequencies S n t past.length)) :
    (Fintype.card (TreeLeafTuple (ZMod Q)ˣ n) : ℝ)⁻¹ *
      (∑ x : TreeLeafTuple (ZMod Q)ˣ n, singleArithmeticLeafSupport n data x) ≤
      ((singleFrequencySplitList S n t).map (singleFrequencySupportBound D)).prod := by
  have hprod : (∏ j ∈ Finset.range (2 ^ n - 1),
      singleFrequencySupportBound D (singleTreeNodeFrequencies S n t j)) =
      ((singleFrequencySplitList S n t).map (singleFrequencySupportBound D)).prod := by
    rw [← singleFrequencySplitList_length S n t]
    exact prod_range_list_getD _ _ _
  unfold singleArithmeticLeafSupport
  rw [treeLeaf_average_by_product (G := (ZMod Q)ˣ) n
    (fun P x => sequentialSupport (fun past y => singleArithmeticSplitTest (data P past) y)
      [] (2 ^ n - 1) (treeLeafSplitEquiv n P x))]
  calc
    _ ≤ (Fintype.card (ZMod Q)ˣ : ℝ)⁻¹ * ∑ _P : (ZMod Q)ˣ,
        ((singleFrequencySplitList S n t).map (singleFrequencySupportBound D)).prod := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun P _ =>
        (single_arithmetic_leaf_support_le (data P) (singleTreeNodeFrequencies S n t) D hD
          (hmatch P) (singleTreeNodeFrequencies_divisor_bound S N D hD hS hdiv n t) n P).trans_eq hprod
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

noncomputable def singleArithmeticSupportSum {Q : ℕ} [NeZero Q]
    (S : Finset ℤ) (V n : ℕ)
    (data : FrequencyTree S n → (ZMod Q)ˣ → List (ZMod Q)ˣ → Option (ArithmeticSplitData Q)) : ℝ :=
  ∑ t : FrequencyTree S n, frequencyLeafWeight (singleFrequencyLeaf S V) n t *
    ((Fintype.card (TreeLeafTuple (ZMod Q)ˣ n) : ℝ)⁻¹ *
      ∑ x : TreeLeafTuple (ZMod Q)ˣ n, singleArithmeticLeafSupport n (data t) x)

/-- The exponent is `2^n`, the number of leaves of one history. Thus its
initial squared weight cancels the entire leading leaf-frequency cost. -/
theorem single_arithmetic_support_sum_le {Q : ℕ} [NeZero Q]
    (S : Finset ℤ) (N V n : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D)
    (data : FrequencyTree S n → (ZMod Q)ˣ → List (ZMod Q)ˣ → Option (ArithmeticSplitData Q))
    (hmatch : ∀ t P past d, data t P past = some d →
      d.hasFrequencies (singleTreeNodeFrequencies S n t past.length)) :
    singleArithmeticSupportSum S V n data ≤
      (4 * D ^ 3 * (1 + Real.log N)) ^ (2 ^ n - 1) * (2 * (V : ℝ)) ^ (2 ^ n) := by
  have hlocal (t : FrequencyTree S n) (P : (ZMod Q)ˣ) :=
    single_arithmetic_leaf_support_le (data t P) (singleTreeNodeFrequencies S n t) D hD
      (hmatch t P) (singleTreeNodeFrequencies_divisor_bound S N D hD hS hdiv n t) n P
  have hprod (t : FrequencyTree S n) :
      (∏ j ∈ Finset.range (2 ^ n - 1),
        singleFrequencySupportBound D (singleTreeNodeFrequencies S n t j)) =
      ((singleFrequencySplitList S n t).map (singleFrequencySupportBound D)).prod := by
    rw [← singleFrequencySplitList_length S n t]
    exact prod_range_list_getD _ _ _
  apply le_trans _ (single_frequency_tree_sum_le S N V n D hD hS
    (gcd_frequency_divisor_bound S N D hS hdiv))
  unfold singleArithmeticSupportSum
  apply Finset.sum_le_sum
  intro t _
  rw [singleFrequencyTreeWeight_eq]
  apply le_trans _ (le_of_eq (mul_comm _ _))
  apply mul_le_mul_of_nonneg_left _ (frequencyLeafWeight_nonneg _
    (fun _ => by unfold singleFrequencyLeaf; split_ifs <;> norm_num) n t)
  unfold singleArithmeticLeafSupport
  rw [treeLeaf_average_by_product (G := (ZMod Q)ˣ) n
    (fun P x => sequentialSupport (fun past y => singleArithmeticSplitTest (data t P past) y)
      [] (2 ^ n - 1) (treeLeafSplitEquiv n P x))]
  calc
    _ ≤ (Fintype.card (ZMod Q)ˣ : ℝ)⁻¹ * ∑ _P : (ZMod Q)ˣ,
        ((singleFrequencySplitList S n t).map (singleFrequencySupportBound D)).prod := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun P _ => (hlocal t P).trans_eq (hprod t)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

end Ostmann

end OAI
