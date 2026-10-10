import OAI.Analysis.LipschitzHilbert.Estimates.SegmentCharging

namespace OAI

/-! The unary-segment negative-power weight sum in §10
`res:segment-weight-sum`. Ratio-sixteen shells give geometric ratio at
most one half for every exponent used by the manuscript. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

private theorem sixteen_rpow_le_half {q : ℝ} (hq : q ≤ -(1 / 4 : ℝ)) :
    (16 : ℝ) ^ q ≤ 1 / 2 := by
  have hfour : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have hsixteen : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, ← Real.rpow_natCast_mul (by norm_num)]
    convert hfour using 1
    norm_num
  have h : (16 : ℝ) ^ (-(1 / 4 : ℝ)) = 1 / 2 := by
    rw [Real.rpow_neg (by norm_num), hsixteen]
    norm_num
  exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) hq).trans_eq h

/-- Finite shell summation from a linear shell-cardinality estimate.
The bound is independent of the number of populated shells. -/
theorem finite_shell_power_sum {ι : Type*} [Fintype ι]
    (mass : ι → ℝ) {M C e : ℝ} (hM : 1 ≤ M) (hC : 0 ≤ C)
    (he : e ≤ -(5 / 4 : ℝ)) (hmass : ∀ i, M ≤ mass i)
    (hcount : ∀ (t : ℝ) (S : Finset ι), M ≤ t →
      (∀ i ∈ S, t ≤ mass i ∧ mass i ≤ 16 * t) → (S.card : ℝ) ≤ C * t) :
    (∑ i, mass i ^ e) ≤ 2 * C * M ^ (e + 1) := by
  classical
  have hM0 : 0 < M := by linarith
  have he0 : e ≤ 0 := by linarith
  have hq : e + 1 ≤ -(1 / 4 : ℝ) := by linarith
  have hex (i : ι) : ∃ r : ℕ, (16 : ℝ) ^ r * M ≤ mass i ∧
      mass i < 16 * ((16 : ℝ) ^ r * M) := by
    obtain ⟨r, hr, hr'⟩ := exists_nat_pow_near
      ((one_le_div hM0).mpr (hmass i)) (by norm_num : (1 : ℝ) < 16)
    refine ⟨r, (le_div_iff₀ hM0).mp hr, ?_⟩
    have h := (div_lt_iff₀ hM0).mp hr'
    rw [pow_succ] at h
    nlinarith
  choose shell hshell using hex
  let R : Finset ℕ := Finset.univ.image shell
  have hR (i : ι) : shell i ∈ R := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hshell_bound (r : ℕ) :
      (∑ i ∈ Finset.univ.filter (fun i => shell i = r), mass i ^ e) ≤
        C * M ^ (e + 1) * (1 / 2 : ℝ) ^ r := by
    let t : ℝ := (16 : ℝ) ^ r * M
    have ht0 : 0 < t := mul_pos (pow_pos (by norm_num) _) hM0
    have htM : M ≤ t := by
      have hp : (1 : ℝ) ≤ 16 ^ r := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 16)
      dsimp [t]
      nlinarith
    have hcard := hcount t (Finset.univ.filter (fun i => shell i = r)) htM (by
      intro i hi
      have hi' : shell i = r := (Finset.mem_filter.mp hi).2
      change (16 : ℝ) ^ r * M ≤ mass i ∧ mass i ≤ 16 * ((16 : ℝ) ^ r * M)
      constructor
      · simpa only [hi'] using (hshell i).1
      · simpa only [hi'] using (hshell i).2.le)
    calc
      _ ≤ ∑ _i ∈ Finset.univ.filter (fun i => shell i = r), t ^ e := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := (Finset.mem_filter.mp hi).2
        exact Real.rpow_le_rpow_of_nonpos ht0 (by simpa [t, hi'] using (hshell i).1) he0
      _ = ((Finset.univ.filter (fun i => shell i = r)).card : ℝ) * t ^ e := by simp
      _ ≤ (C * t) * t ^ e :=
        mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg ht0.le _)
      _ = C * M ^ (e + 1) * ((16 : ℝ) ^ (e + 1)) ^ r := by
        rw [show (C * t) * t ^ e = C * t ^ (e + 1) by
          rw [Real.rpow_add_one ht0.ne']; ring]
        dsimp [t]
        rw [Real.mul_rpow (by positivity) hM0.le, ← Real.rpow_pow_comm (by norm_num)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) (sixteen_rpow_le_half hq) r)
        (by positivity)
  calc
    _ = ∑ r ∈ R, ∑ i ∈ Finset.univ.filter (fun i => shell i = r), mass i ^ e :=
      (Finset.sum_fiberwise_of_maps_to (fun i _ => hR i) _).symm
    _ ≤ ∑ r ∈ R, C * M ^ (e + 1) * (1 / 2 : ℝ) ^ r :=
      Finset.sum_le_sum fun r _ => hshell_bound r
    _ = (C * M ^ (e + 1)) * ∑ r ∈ R, (1 / 2 : ℝ) ^ r := (Finset.mul_sum ..).symm
    _ ≤ (C * M ^ (e + 1)) * 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (summable_geometric_two.sum_le_tsum R (fun r _ => by positivity)).trans_eq
        tsum_geometric_two
    _ = _ := by ring

/-- The exact `3/2` weight exponent needed by Hölder against the good-path
cubic variation bound, with its shell hypothesis discharged by charges. -/
theorem charged_segment_weight_sum {ι : Type*} [Fintype ι]
    (mass : ι → ℝ) (charge : ι → Option ℕ) (n : ℕ → ℝ)
    (hn : Antitone n) (hinj : Function.Injective charge)
    {c M μ : ℝ} (hc : 0 < c) (hM : 1 ≤ M) (hμ : μ ≤ 1 / 12)
    (hmass : ∀ i, M ≤ mass i)
    (hcharge : ∀ i k, charge i = some k →
      mass i - 2 ≤ n k ∧ n k ≤ mass i ∧ c ≤ n k - n (k + 1)) :
    (∑ i, mass i ^ ((-1 + μ) * (3 / 2 : ℝ))) ≤
      2 * (2 + 17 / c) * M ^ (-(1 / 2 : ℝ) + 3 * μ / 2) := by
  have h := finite_shell_power_sum mass hM
    (show 0 ≤ 2 + 17 / c by positivity)
    (show (-1 + μ) * (3 / 2 : ℝ) ≤ -(5 / 4 : ℝ) by linarith) hmass
    (fun t S ht hS => charged_segment_shell_linear mass charge n hn hinj hc
      (hM.trans ht) hcharge S hS)
  have hexp : (-1 + μ) * (3 / 2 : ℝ) + 1 = -(1 / 2 : ℝ) + 3 * μ / 2 := by ring
  simpa only [hexp] using h

end LipschitzHilbert

end

end OAI
