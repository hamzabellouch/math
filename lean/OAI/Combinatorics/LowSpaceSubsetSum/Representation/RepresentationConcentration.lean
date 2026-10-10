import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionConcentration

namespace OAI

/-!
# The low-mean layout event

These estimates concern one uniform permutation of a fixed layout. All six
half blocks and all three mixers have the required marginals without any
independence assumption. The spread test retains the integer floor used by
the program. The separate balance law connects this layout law to the
conditional signed-solution experiment.
-/

namespace LowSpaceSubsetSum

open scoped BigOperators

theorem finiteUniformProbability_union_le {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P Q : Ω → Prop) :
    finiteUniformProbability (fun ω => P ω ∨ Q ω) ≤
      finiteUniformProbability P + finiteUniformProbability Q := by
  have h := finiteUniformProbability_exists_le_sum
    (fun (b : Bool) (ω : Ω) => if b then P ω else Q ω)
  simpa [Bool.exists_bool, Fintype.sum_bool, or_comm, add_comm] using h

/-- The exact pairwise integer spread test; it also bounds the largest list
by the smallest list times the displayed factor. -/
def mixerSpreadTest {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℤ)
    (M : Fin 3 → Finset ι) (n : ℕ) : Prop :=
  ∀ i j, distinctSumCount a (M i) ≤ distinctSumCount a (M j) * 2 ^ (n / 2000)

theorem spread_floor_margin {n : ℕ} (hn : 10000 ≤ n) :
    (n : ℝ) / 2500 ≤ (n / 2000 : ℕ) := by
  have hrem := Nat.mod_lt n (by norm_num : 0 < 2000)
  have hdiv := Nat.mod_add_div n 2000
  have hnR : (10000 : ℝ) ≤ n := by exact_mod_cast hn
  have hfloor : (n : ℝ) < 2000 * ((n / 2000 : ℕ) + 1 : ℝ) := by
    exact_mod_cast (show n < 2000 * (n / 2000 + 1) by omega)
  linarith

theorem mixerSpreadTest_of_centered {n m : ℕ} (hn : 10000 ≤ n)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℤ) (M : Fin 3 → Finset ι)
    (hM : ∀ i, (M i).card = m) (ν : ℝ)
    (hcenter : ∀ i, |deficiency a (M i) - ν| ≤ (n : ℝ) / 5000) :
    mixerSpreadTest a M n := by
  intro i j
  have hi := (abs_le.mp (hcenter i)).1
  have hj := (abs_le.mp (hcenter j)).2
  have hfloor := spread_floor_margin hn
  have hexp : ((M i).card : ℝ) - deficiency a (M i) ≤
      ((M j).card : ℝ) - deficiency a (M j) + (n / 2000 : ℕ) := by
    rw [hM i, hM j]
    linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    two_pow_card_sub_deficiency, two_pow_card_sub_deficiency,
    Real.rpow_natCast] at hpow
  exact_mod_cast hpow

/-- Simultaneous concentration for the six halves and three pre-order
mixers. This is a marginal union bound, with explicit absolute threshold. -/
theorem representation_layout_good_probability {n s m : ℕ} (hn : 0 < n)
    (hs : (s : ℝ) ≤ (3 / 25 : ℝ) * n)
    (hm : (m : ℝ) ≤ (6 / 25 : ℝ) * n)
    (a : Fin n → ℤ) (H : Fin 6 → Finset (Fin n))
    (M : Fin 3 → Finset (Fin n))
    (hH : ∀ i, (H i).card = s) (hM : ∀ i, (M i).card = m)
    (hmean : meanDeficiency a Finset.univ s < (153 / 20000 : ℝ) * n) :
    1 - (90000000 : ℝ) / n ≤ finiteUniformProbability (fun e : Equiv.Perm (Fin n) =>
      (∀ i, deficiency a (permuteSubset e (H i)) ≤ (39 / 5000 : ℝ) * n) ∧
      (∀ i, |deficiency a (permuteSubset e (M i)) -
        meanDeficiency a Finset.univ m| ≤ (n : ℝ) / 5000)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hhalf (i : Fin 6) : finiteUniformProbability (fun e : Equiv.Perm (Fin n) =>
      (39 / 5000 : ℝ) * n < deficiency a (permuteSubset e (H i))) ≤
        (12000000 : ℝ) / n := by
    have hinc : ∀ e : Equiv.Perm (Fin n),
        (39 / 5000 : ℝ) * n < deficiency a (permuteSubset e (H i)) →
        (n : ℝ) / 10000 ≤ |deficiency a (permuteSubset e (H i)) -
          meanDeficiency a Finset.univ s| := by
      intro e he
      have habs := le_abs_self
        (deficiency a (permuteSubset e (H i)) - meanDeficiency a Finset.univ s)
      linarith
    apply (finiteUniformProbability_mono hinc).trans
    have htail := permutation_deficiency_tail a (H i)
      (show 0 < (n : ℝ) / 10000 by positivity)
    rw [hH i] at htail
    apply htail.trans
    calc
      (s : ℝ) / ((n : ℝ) / 10000) ^ 2 ≤
          ((3 / 25 : ℝ) * n) / ((n : ℝ) / 10000) ^ 2 :=
        div_le_div_of_nonneg_right hs (sq_nonneg _)
      _ = (12000000 : ℝ) / n := by field_simp; ring
  have hmixer (i : Fin 3) : finiteUniformProbability (fun e : Equiv.Perm (Fin n) =>
      (n : ℝ) / 5000 < |deficiency a (permuteSubset e (M i)) -
        meanDeficiency a Finset.univ m|) ≤ (6000000 : ℝ) / n := by
    have hinc : ∀ e : Equiv.Perm (Fin n),
        (n : ℝ) / 5000 < |deficiency a (permuteSubset e (M i)) -
          meanDeficiency a Finset.univ m| →
        (n : ℝ) / 5000 ≤ |deficiency a (permuteSubset e (M i)) -
          meanDeficiency a Finset.univ m| := fun _ he => he.le
    apply (finiteUniformProbability_mono hinc).trans
    have htail := permutation_deficiency_tail a (M i)
      (show 0 < (n : ℝ) / 5000 by positivity)
    rw [hM i] at htail
    apply htail.trans
    calc
      (m : ℝ) / ((n : ℝ) / 5000) ^ 2 ≤
          ((6 / 25 : ℝ) * n) / ((n : ℝ) / 5000) ^ 2 :=
        div_le_div_of_nonneg_right hm (sq_nonneg _)
      _ = (6000000 : ℝ) / n := by field_simp; ring
  have hhalves := (finiteUniformProbability_exists_le_sum
    (fun (i : Fin 6) (e : Equiv.Perm (Fin n)) =>
      (39 / 5000 : ℝ) * n < deficiency a (permuteSubset e (H i)))).trans
    (Finset.sum_le_sum (fun i _ => hhalf i))
  have hmixers := (finiteUniformProbability_exists_le_sum
    (fun (i : Fin 3) (e : Equiv.Perm (Fin n)) =>
      (n : ℝ) / 5000 < |deficiency a (permuteSubset e (M i)) -
        meanDeficiency a Finset.univ m|)).trans
    (Finset.sum_le_sum (fun i _ => hmixer i))
  have hbad := (finiteUniformProbability_union_le
    (fun e : Equiv.Perm (Fin n) => ∃ i,
      (39 / 5000 : ℝ) * n < deficiency a (permuteSubset e (H i)))
    (fun e : Equiv.Perm (Fin n) => ∃ i, (n : ℝ) / 5000 <
      |deficiency a (permuteSubset e (M i)) - meanDeficiency a Finset.univ m|)).trans
    (add_le_add hhalves hmixers)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hbad
  norm_num at hbad
  have hsum : (6 : ℝ) * (12000000 / (n : ℝ)) + 3 * (6000000 / (n : ℝ)) =
      90000000 / (n : ℝ) := by ring
  rw [hsum] at hbad
  have hcompl : (fun e : Equiv.Perm (Fin n) =>
      (∀ i, deficiency a (permuteSubset e (H i)) ≤ (39 / 5000 : ℝ) * n) ∧
      (∀ i, |deficiency a (permuteSubset e (M i)) -
        meanDeficiency a Finset.univ m| ≤ (n : ℝ) / 5000)) =
      (fun e => ¬((∃ i, (39 / 5000 : ℝ) * n < deficiency a (permuteSubset e (H i))) ∨
        (∃ i, (n : ℝ) / 5000 < |deficiency a (permuteSubset e (M i)) -
          meanDeficiency a Finset.univ m|))) := by
    ext e
    simp only [not_or, not_exists, not_lt]
  rw [hcompl, finiteUniformProbability_compl]
  linarith

theorem representation_layout_tests_probability {n s m : ℕ} (hn : 180000000 ≤ n)
    (hs : (s : ℝ) ≤ (3 / 25 : ℝ) * n)
    (hm : (m : ℝ) ≤ (6 / 25 : ℝ) * n)
    (a : Fin n → ℤ) (H : Fin 6 → Finset (Fin n))
    (M : Fin 3 → Finset (Fin n))
    (hH : ∀ i, (H i).card = s) (hM : ∀ i, (M i).card = m)
    (hmean : meanDeficiency a Finset.univ s < (153 / 20000 : ℝ) * n) :
    (1 / 2 : ℝ) ≤ finiteUniformProbability (fun e : Equiv.Perm (Fin n) =>
      (∀ i, deficiency a (permuteSubset e (H i)) ≤ (39 / 5000 : ℝ) * n) ∧
      mixerSpreadTest a (fun i => permuteSubset e (M i)) n) := by
  have hgood := representation_layout_good_probability (by omega : 0 < n)
    hs hm a H M hH hM hmean
  have hnR : (180000000 : ℝ) ≤ n := by exact_mod_cast hn
  have hhalf : (1 / 2 : ℝ) ≤ 1 - (90000000 : ℝ) / n := by
    have hd : (90000000 : ℝ) / n ≤ 1 / 2 := by
      apply (div_le_iff₀ (by linarith : (0 : ℝ) < n)).mpr
      linarith
    linarith
  apply (hhalf.trans hgood).trans
  apply finiteUniformProbability_mono
  intro e he
  exact ⟨he.1, mixerSpreadTest_of_centered (by omega) a _
    (fun i => by rw [permuteSubset_card, hM i]) _ he.2⟩

end LowSpaceSubsetSum

end OAI
