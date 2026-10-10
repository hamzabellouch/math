import OAI.NumberTheory.Ostmann.Arithmetic.FrequencyTreeNodes

namespace OAI

/-! # The frequency budget for one squared history

Unlike a pair of histories, this sum has exactly one frequency at each leaf.
This is needed before the level-zero square-weight cancellation.
-/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def singleFrequencyKernel (S : Finset ℤ) (D : ℝ)
    (root left right : S) : ℝ :=
  2 * D ^ 2 / reducedFrequency ((left : ℤ).natAbs.gcd (right : ℤ).natAbs) (root : ℤ).natAbs

noncomputable def singleFrequencyLeaf (S : Finset ℤ) (V : ℕ) (x : S) : ℝ :=
  if (x : ℤ).natAbs ≤ V then 1 else 0

theorem signed_reducedFrequency_sum_le (S : Finset ℤ) (N g : ℕ)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N) (hg : g ≠ 0) :
    (∑ s ∈ S, ((reducedFrequency g s.natAbs : ℕ) : ℝ)⁻¹) ≤
      2 * (g.divisors.card : ℝ) * (1 + Real.log N) := by
  have hh : (∑ a ∈ Finset.Icc 1 N, (a : ℝ)⁻¹) ≤ 1 + Real.log N := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using harmonic_le_one_add_log N
  calc
    _ ≤ 2 * ∑ a ∈ Finset.Icc 1 N, ((reducedFrequency g a : ℕ) : ℝ)⁻¹ :=
      sum_signed_magnitudes_le S N hS _ (fun _ _ => by positivity)
    _ ≤ 2 * ((g.divisors.card : ℝ) * ∑ a ∈ Finset.Icc 1 N, (a : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (sum_reducedFrequency_le N g hg
        (fun a => (a : ℝ)⁻¹) (fun _ _ => by positivity)) (by norm_num)
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_left hh (show 0 ≤ (g.divisors.card : ℝ) by positivity)
      nlinarith

theorem singleFrequencyKernel_sum_le (S : Finset ℤ) (N : ℕ) (D : ℝ)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (hdiv : ∀ v ∈ S, ∀ w ∈ S, ((v.natAbs.gcd w.natAbs).divisors.card : ℝ) ≤ D)
    (left right : S) :
    (∑ root : S, singleFrequencyKernel S D root left right) ≤
      4 * D ^ 3 * (1 + Real.log N) := by
  let g := (left : ℤ).natAbs.gcd (right : ℤ).natAbs
  have hg : g ≠ 0 := Nat.ne_of_gt (Nat.gcd_pos_of_pos_left _
    (Int.natAbs_pos.mpr (hS _ left.property).1))
  have hb := signed_reducedFrequency_sum_le S N g hS hg
  have hd : (g.divisors.card : ℝ) ≤ D := hdiv _ left.property _ right.property
  calc
    _ = 2 * D ^ 2 * (∑ s ∈ S, ((reducedFrequency g s.natAbs : ℕ) : ℝ)⁻¹) := by
      unfold singleFrequencyKernel
      simp only [div_eq_mul_inv, ← Finset.mul_sum]
      rw [Finset.sum_coe_sort S (fun s : ℤ => ((reducedFrequency g s.natAbs : ℕ) : ℝ)⁻¹)]
    _ ≤ 2 * D ^ 2 * (2 * (g.divisors.card : ℝ) * (1 + Real.log N)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ 2 * D ^ 2 * (2 * D * (1 + Real.log N)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by norm_num))
        (by have := Real.log_natCast_nonneg N; positivity)
    _ = _ := by ring

theorem singleFrequencyLeaf_sum_le (S : Finset ℤ) (V : ℕ)
    (hS : ∀ s ∈ S, s ≠ 0) :
    (∑ x : S, singleFrequencyLeaf S V x) ≤ 2 * V := by
  let T := S.filter fun s => s.natAbs ≤ V
  have hT : ∀ s ∈ T, s ≠ 0 ∧ s.natAbs ≤ V := by
    intro s hs
    exact ⟨hS s (Finset.mem_filter.mp hs).1, (Finset.mem_filter.mp hs).2⟩
  have hb := sum_signed_magnitudes_le T V hT (fun _ => (1 : ℝ)) (by intros; norm_num)
  unfold singleFrequencyLeaf
  rw [Finset.sum_coe_sort S (fun s : ℤ => if s.natAbs ≤ V then (1 : ℝ) else 0)]
  simpa [← Finset.sum_filter, T] using hb

theorem single_frequency_tree_sum_le (S : Finset ℤ) (N V n : ℕ) (D : ℝ)
    (hD : 0 ≤ D) (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (hdiv : ∀ v ∈ S, ∀ w ∈ S, ((v.natAbs.gcd w.natAbs).divisors.card : ℝ) ≤ D) :
    (∑ x : FrequencyTree S n,
      frequencyTreeWeight (singleFrequencyKernel S D) (singleFrequencyLeaf S V) n x) ≤
      (4 * D ^ 3 * (1 + Real.log N)) ^ (2 ^ n - 1) * (2 * (V : ℝ)) ^ (2 ^ n) := by
  have hC : 0 ≤ 4 * D ^ 3 * (1 + Real.log N) := by
    have := Real.log_natCast_nonneg N
    positivity
  apply (frequencyTree_sum_le (singleFrequencyKernel S D) (singleFrequencyLeaf S V)
    _ (by intros; unfold singleFrequencyKernel; positivity)
    (by intros; unfold singleFrequencyLeaf; split_ifs <;> norm_num) hC
    (singleFrequencyKernel_sum_le S N D hS hdiv) n).trans
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Finset.sum_nonneg fun x _ => by
      unfold singleFrequencyLeaf; split_ifs <;> norm_num)
      (singleFrequencyLeaf_sum_le S V (fun s hs => (hS s hs).1)) _) (pow_nonneg hC _)

def singleFrequencySplitList (S : Finset ℤ) : (n : ℕ) →
    FrequencyTree S n → List NodeFrequencies
  | 0, _ => []
  | n + 1, x => ⟨x.1, (frequencyRoot n x.2.1 : S), (frequencyRoot n x.2.2 : S)⟩ ::
      (singleFrequencySplitList S n x.2.1 ++ singleFrequencySplitList S n x.2.2)

theorem singleFrequencySplitList_length (S : Finset ℤ) (n : ℕ) (x : FrequencyTree S n) :
    (singleFrequencySplitList S n x).length = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [singleFrequencySplitList, List.length_cons, List.length_append, ih]
    have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [pow_succ]
    omega

noncomputable def singleFrequencySupportBound (D : ℝ) (f : NodeFrequencies) : ℝ :=
  2 * D ^ 2 / f.reducedModulus

theorem singleFrequencyTreeWeight_eq (S : Finset ℤ) (D : ℝ) (W : S → ℝ)
    (n : ℕ) (x : FrequencyTree S n) :
    frequencyTreeWeight (singleFrequencyKernel S D) W n x =
      ((singleFrequencySplitList S n x).map (singleFrequencySupportBound D)).prod *
        frequencyLeafWeight W n x := by
  induction n with
  | zero => simp [frequencyTreeWeight, singleFrequencySplitList, frequencyLeafWeight]
  | succ n ih =>
    simp only [frequencyTreeWeight, singleFrequencySplitList, frequencyLeafWeight,
      List.map_cons, List.map_append, List.prod_cons, List.prod_append, ih,
      singleFrequencySupportBound, singleFrequencyKernel, NodeFrequencies.reducedModulus]
    ring

def singleTreeNodeFrequencies (S : Finset ℤ) (n : ℕ) (x : FrequencyTree S n)
    (j : ℕ) : NodeFrequencies :=
  (singleFrequencySplitList S n x).getD j emptyNodeFrequencies

theorem singleFrequencySplitList_modulus_mem (S : Finset ℤ) (N : ℕ)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N) (n : ℕ) (x : FrequencyTree S n)
    (f : NodeFrequencies) (hf : f ∈ singleFrequencySplitList S n x) :
    f.reducedModulus ∈ Finset.Icc 1 N := by
  induction n with
  | zero => simp [singleFrequencySplitList] at hf
  | succ n ih =>
    simp only [singleFrequencySplitList, List.mem_cons, List.mem_append] at hf
    rcases hf with rfl | hf | hf
    · exact reducedFrequency_mem (Finset.mem_Icc.mpr
        ⟨Int.natAbs_pos.mpr (hS _ x.1.property).1, (hS _ x.1.property).2⟩)
    · exact ih _ hf
    · exact ih _ hf

theorem singleTreeNodeFrequencies_divisor_bound (S : Finset ℤ) (N : ℕ) (D : ℝ)
    (hD : 0 ≤ D) (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D)
    (n : ℕ) (x : FrequencyTree S n) (j : ℕ) :
    (((singleTreeNodeFrequencies S n x j).reducedModulus).divisors.card : ℝ) ≤ D := by
  by_cases hj : j < (singleFrequencySplitList S n x).length
  · have hmem : singleTreeNodeFrequencies S n x j ∈ singleFrequencySplitList S n x := by
      rw [singleTreeNodeFrequencies, List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    obtain ⟨hpos, hle⟩ := Finset.mem_Icc.mp (singleFrequencySplitList_modulus_mem S N hS n x _ hmem)
    apply hdiv _ (Nat.ne_of_gt hpos)
    exact hle.trans (by nlinarith)
  · rw [singleTreeNodeFrequencies, List.getD_eq_default _ _ (by omega)]
    simpa [emptyNodeFrequencies, NodeFrequencies.reducedModulus, reducedFrequency] using hD

end Ostmann

end OAI
