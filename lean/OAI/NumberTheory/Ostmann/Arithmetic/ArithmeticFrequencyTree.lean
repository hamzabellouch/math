import OAI.NumberTheory.Ostmann.Arithmetic.FrequencyTreeSum
import OAI.NumberTheory.Ostmann.Characters.SignedFrequencySum

namespace OAI

/-! # The full arithmetic frequency-tree budget -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def pairedFrequencyKernel (S : Finset ℤ) (D : ℝ)
    (root left right : S × S) : ℝ :=
  2 * D ^ 2 *
    (((reducedFrequency ((left.1 : ℤ).natAbs.gcd (right.1 : ℤ).natAbs) (root.1 : ℤ).natAbs).lcm
       (reducedFrequency ((left.2 : ℤ).natAbs.gcd (right.2 : ℤ).natAbs) (root.2 : ℤ).natAbs) : ℕ) : ℝ)⁻¹

theorem pairedFrequencyKernel_sum_le (S : Finset ℤ) (N : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (hdiv : ∀ v ∈ S, ∀ w ∈ S, ((v.natAbs.gcd w.natAbs).divisors.card : ℝ) ≤ D)
    (left right : S × S) :
    (∑ root : S × S, pairedFrequencyKernel S D root left right) ≤
      8 * D ^ 4 * (1 + Real.log N) ^ 3 := by
  let g := (left.1 : ℤ).natAbs.gcd (right.1 : ℤ).natAbs
  let h := (left.2 : ℤ).natAbs.gcd (right.2 : ℤ).natAbs
  have hg : g ≠ 0 := Nat.ne_of_gt (Nat.gcd_pos_of_pos_left _
    (Int.natAbs_pos.mpr (hS _ left.1.property).1))
  have hh : h ≠ 0 := Nat.ne_of_gt (Nat.gcd_pos_of_pos_left _
    (Int.natAbs_pos.mpr (hS _ left.2.property).1))
  have hgd : (g.divisors.card : ℝ) ≤ D := hdiv _ left.1.property _ right.1.property
  have hhd : (h.divisors.card : ℝ) ≤ D := hdiv _ left.2.property _ right.2.property
  have hpair :
      (∑ s : S, ∑ t : S,
        (((reducedFrequency g (s : ℤ).natAbs).lcm (reducedFrequency h (t : ℤ).natAbs) : ℕ) : ℝ)⁻¹) =
      ∑ s ∈ S, ∑ t ∈ S,
        (((reducedFrequency g s.natAbs).lcm (reducedFrequency h t.natAbs) : ℕ) : ℝ)⁻¹ := by
    rw [Finset.sum_coe_sort S (fun s : ℤ => ∑ t : S,
      (((reducedFrequency g s.natAbs).lcm (reducedFrequency h (t : ℤ).natAbs) : ℕ) : ℝ)⁻¹)]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_coe_sort S (fun t : ℤ =>
      (((reducedFrequency g s.natAbs).lcm (reducedFrequency h t.natAbs) : ℕ) : ℝ)⁻¹)
  calc
    _ = 2 * D ^ 2 * (∑ s : S, ∑ t : S,
        (((reducedFrequency g (s : ℤ).natAbs).lcm (reducedFrequency h (t : ℤ).natAbs) : ℕ) : ℝ)⁻¹) := by
      simp only [pairedFrequencyKernel, Fintype.sum_prod_type, ← Finset.mul_sum, g, h]
    _ ≤ 2 * D ^ 2 * (4 * (g.divisors.card : ℝ) * h.divisors.card * (1 + Real.log N) ^ 3) := by
      rw [hpair]
      exact mul_le_mul_of_nonneg_left (signed_reducedFrequency_lcm_sum_le S S N g h hS hS hg hh)
        (by positivity)
    _ ≤ 2 * D ^ 2 * (4 * D * D * (1 + Real.log N) ^ 3) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hlog : 0 ≤ (1 + Real.log N) ^ 3 := by
        have hbase := Real.log_natCast_nonneg N
        positivity
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_left hgd (by norm_num)) hhd
          (Nat.cast_nonneg _) (by positivity)) hlog
    _ = _ := by ring

noncomputable def pairedFrequencyLeaf (S : Finset ℤ) (V : ℕ) (x : S × S) : ℝ :=
  if (x.1 : ℤ).natAbs ≤ V ∧ (x.2 : ℤ).natAbs ≤ V then 1 else 0

theorem pairedFrequencyLeaf_sum_le (S : Finset ℤ) (V : ℕ)
    (hS : ∀ s ∈ S, s ≠ 0) :
    (∑ x : S × S, pairedFrequencyLeaf S V x) ≤ (2 * (V : ℝ)) ^ 2 := by
  let T := S.filter fun s => s.natAbs ≤ V
  have hT : ∀ s ∈ T, s ≠ 0 ∧ s.natAbs ≤ V := by
    intro s hs
    exact ⟨hS s (Finset.mem_filter.mp hs).1, (Finset.mem_filter.mp hs).2⟩
  have hcard : (T.card : ℝ) ≤ 2 * V := by
    have hbound := sum_signed_magnitudes_le T V hT (fun _ => (1 : ℝ)) (by intros; norm_num)
    simpa using hbound
  have hsingle : (∑ s : S, if (s : ℤ).natAbs ≤ V then (1 : ℝ) else 0) = T.card := by
    rw [Finset.sum_coe_sort S (fun s : ℤ => if s.natAbs ≤ V then (1 : ℝ) else 0)]
    simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, T]
  have hterm (x y : S) : pairedFrequencyLeaf S V (x, y) =
      (if (x : ℤ).natAbs ≤ V then (1 : ℝ) else 0) *
        (if (y : ℤ).natAbs ≤ V then (1 : ℝ) else 0) := by
    unfold pairedFrequencyLeaf
    split_ifs <;> simp_all
  calc
    _ = (T.card : ℝ) ^ 2 := by
      rw [Fintype.sum_prod_type, pow_two, ← hsingle, Finset.sum_mul_sum]
      simp only [hterm]
    _ ≤ _ := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2

/-- Root-first elimination leaves only the two histories' leaf frequencies.
The exponent `2^n-1` is the exact number of internal nodes. -/
theorem arithmetic_frequency_tree_sum_le (S : Finset ℤ) (N V : ℕ) (D : ℝ)
    (hD : 0 ≤ D) (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (hdiv : ∀ v ∈ S, ∀ w ∈ S, ((v.natAbs.gcd w.natAbs).divisors.card : ℝ) ≤ D)
    (n : ℕ) :
    (∑ x : FrequencyTree (S × S) n,
      frequencyTreeWeight (pairedFrequencyKernel S D) (pairedFrequencyLeaf S V) n x) ≤
      (8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (2 ^ n - 1) * (2 * (V : ℝ)) ^ (2 * 2 ^ n) := by
  have hC : 0 ≤ 8 * D ^ 4 * (1 + Real.log N) ^ 3 := by
    have hlog := Real.log_natCast_nonneg N
    positivity
  have hmain := frequencyTree_sum_le (pairedFrequencyKernel S D) (pairedFrequencyLeaf S V)
    (8 * D ^ 4 * (1 + Real.log N) ^ 3) (by intros; unfold pairedFrequencyKernel; positivity)
    (by intros; unfold pairedFrequencyLeaf; split_ifs <;> norm_num) hC
    (pairedFrequencyKernel_sum_le S N D hD hS hdiv) n
  apply hmain.trans
  have hleaf := pairedFrequencyLeaf_sum_le S V (fun s hs => (hS s hs).1)
  calc
    _ ≤ (8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (2 ^ n - 1) *
        ((2 * (V : ℝ)) ^ 2) ^ (2 ^ n) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀
        (Finset.sum_nonneg fun x _ => by unfold pairedFrequencyLeaf; split_ifs <;> norm_num)
        hleaf _) (pow_nonneg hC _)
    _ = _ := by rw [← pow_mul]

end Ostmann

end OAI
