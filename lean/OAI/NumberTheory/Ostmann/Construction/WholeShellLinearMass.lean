import OAI.NumberTheory.Ostmann.Construction.WholeShellMass

namespace OAI

/-! # Linear harmonic mass in the full original bulk shell -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem logPrimeBand_mass_quarter {C : ℝ} (hM : MertensEstimate C)
    (u : ℝ) (hu : 1 ≤ u) (he : 2 * (Real.log 2 + 2 * C) ≤ u) :
    (1 / 4 : ℝ) ≤ ∑ p ∈ logPrimeBand u, (p : ℝ)⁻¹ := by
  have hw := (logPrimeBand_weight_bounds u C hu hM).1
  have hb : (∑ p ∈ logPrimeBand u, Real.log (p : ℝ) / p) ≤
      (2 * u) * ∑ p ∈ logPrimeBand u, (p : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    simpa only [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_right (logPrimeBand_mem hp).2.2 (by positivity : 0 ≤ (p : ℝ)⁻¹)
  nlinarith

theorem whole_shell_geometric_mass {C : ℝ} (hM : MertensEstimate C)
    (u v : ℝ) (hu : 1 ≤ u) (he : 2 * (Real.log 2 + 2 * C) ≤ u)
    (N : ℕ) (hN : (2 : ℝ) ^ N * u ≤ v) :
    (N : ℝ) / 4 ≤ ∑ p ∈ primeLogCellSet 1 0 u v, (p : ℝ)⁻¹ := by
  let B := fun i : Fin N => logPrimeBand ((2 : ℝ) ^ i.val * u)
  have hpow (i : ℕ) : u ≤ (2 : ℝ) ^ i * u :=
    le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num))
  have hband (i : Fin N) : (1 / 4 : ℝ) ≤ ∑ p ∈ B i, (p : ℝ)⁻¹ :=
    logPrimeBand_mass_quarter hM _ (hu.trans (hpow _)) (he.trans (hpow _))
  have hdisj (i j : Fin N) (hij : i.val < j.val) : Disjoint (B i) (B j) := by
    apply Finset.disjoint_left.mpr
    intro p hi hj
    have hip := (logPrimeBand_mem hi).2.2
    have hjp := (logPrimeBand_mem hj).2.1
    have hp := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.succ_le_of_lt hij)) (by linarith : 0 ≤ u)
    rw [pow_succ] at hp
    nlinarith
  have hpair : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin N))) B := by
    intro i _ j _ hij
    rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun h => hij (Fin.ext h)) with h | h
    · exact hdisj i j h
    · exact (hdisj j i h).symm
  have hsub : (Finset.univ.biUnion B) ⊆ primeLogCellSet 1 0 u v := by
    intro p hp
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hprime, hlo, hhi⟩ := logPrimeBand_mem hi
    apply mem_primeLogCellSet_iff.mpr
    refine ⟨hprime, by simp only [Nat.modEq_one], (hpow i.val).trans_lt hlo, ?_⟩
    have hp := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.succ_le_of_lt i.isLt)) (by linarith : 0 ≤ u)
    rw [pow_succ] at hp
    exact hhi.trans ((by nlinarith : 2 * ((2 : ℝ) ^ i.val * u) ≤ (2 : ℝ) ^ N * u).trans hN)
  calc
    (N : ℝ) / 4 = ∑ _i : Fin N, (1 / 4 : ℝ) := by simp; ring
    _ ≤ ∑ i : Fin N, ∑ p ∈ B i, (p : ℝ)⁻¹ := Finset.sum_le_sum (fun i _ => hband i)
    _ = ∑ p ∈ Finset.univ.biUnion B, (p : ℝ)⁻¹ := (Finset.sum_biUnion hpair).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

theorem whole_shell_linear_mass {C : ℝ} (hM : MertensEstimate C) :
    ∀ᶠ L : ℝ in atTop, L / 8000 ≤
      ∑ p ∈ primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L)), (p : ℝ)⁻¹ := by
  have ht := (Real.tendsto_exp_atTop.comp
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 4 / 1000))).eventually
      (eventually_ge_atTop (2 * (Real.log 2 + 2 * C)))
  filter_upwards [ht, eventually_ge_atTop (2000 : ℝ)] with L hlarge hL
  let N : ℕ := ⌊L / 1000⌋₊
  have hL0 : 0 ≤ L := by linarith
  have hNu : (N : ℝ) ≤ L / 1000 := Nat.floor_le (by positivity)
  have hNl : L / 1000 - 1 < (N : ℝ) := Nat.sub_one_lt_floor _
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hp : (2 : ℝ) ^ N = Real.exp ((N : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hN : (2 : ℝ) ^ N * Real.exp ((4 / 1000 : ℝ) * L) ≤
      Real.exp ((6 / 1000 : ℝ) * L) := by
    rw [hp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hn := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg N (α := ℝ))
    nlinarith
  have hmass := whole_shell_geometric_mass hM
    (Real.exp ((4 / 1000 : ℝ) * L)) (Real.exp ((6 / 1000 : ℝ) * L))
    (Real.one_le_exp (by positivity)) hlarge N hN
  linarith

end Ostmann

end OAI
